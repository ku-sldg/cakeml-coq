From TLC Require Import LibLogic LibReflect.
Require Import CakeSem.CakeAST.
Require Import CakeSem.Namespace.
Require Import CakeSem.SemanticPrimitives.
Require Import CakeSem.ffi.FFI.
Require Import CakeSem.Utils.

Require Import PeanoNat.
Require Import List.
Import ListNotations.

Definition fix_clock {ffi' : Type} {res error : Type} (s : state ffi')
           (p : state ffi' * result res error) : state ffi' * result res error :=
  match p with (s', r) =>
               ({| clock := If clock s' <= clock s
                           then clock s' else clock s;
                   refs := refs s';
                   ffi := ffi s';
                   next_type_stamp := next_type_stamp s';
                   next_exn_stamp := next_exn_stamp s' |}
                , r)
  end.

Definition dec_clock {ffi' : Type} (s : state ffi') : state ffi' :=
  {| clock := clock s - 1;
     refs := refs s;
     ffi := ffi s;
     next_type_stamp := next_type_stamp s;
     next_exn_stamp := next_exn_stamp s |}.

Definition list_result {A B : Type} (res : result A B) : result (list A) B :=
  match res with
  | Rval v => Rval [v]
  | Rerr e => Rerr e
  end.

Definition v : Type := val. (* TODO: why? *)

(* LATER: fix decreasing measure, e.g. using TLC's LibFix, or fuel argument *)

Fixpoint evaluate {ffi' : Type} (st : state ffi') (env : sem_env v)
         (es : list exp) : state ffi' * result (list v) v :=

  let fix evaluate_match (st : state ffi') (env : sem_env v) (v' : v)
          (pes : list (pat * exp)) (err_v : v) : state ffi' * result (list v) v :=
      match pes with
      | [] => (st, Rerr (Rraise err_v))
      | (p,e)::pes' => If LibList.noduplicates (pat_bindings p [])
                     then match pmatch (sec env) (refs st) p v' [] with
                          | Match env_v' => evaluate st {| sev := nsAppend (alist_to_ns env_v') (sev env);
                                                          sec := (sec env) |} [e]
                          | No_match => evaluate_match st env v' pes' err_v
                          | Match_type_error => (st, Rerr (Rabort Rtype_error))
                          end
                     else (st, Rerr (Rabort Rtype_error))
      end
  in

  let fix evaluate_single_exp (st : state ffi') (env : sem_env v) (ex : exp)
      : state ffi' * result (list v) v :=
      match ex with
      | ELit l => (st, Rval [Litv l])
      | ERaise e => match evaluate_single_exp st env e with
                  | (st', Rval (v'::vs')) => (st', Rerr (Rraise v'))
                  | res => res
                  end
      | EHandle e pes => match (evaluate_single_exp st env e) with
                       | (st', Rerr (Rraise v')) => evaluate_match st' env v' pes v'
                       | res => res
                       end
      | ECon cn es' => if do_con_check (sec env) cn (length es')
                     then match evaluate st env (rev es') with
                          | (st', Rval vs) => match build_conv (sec env) cn (rev vs) with
                                             | Some v' => (st', Rval [v'])
                                             | None => (st', Rerr (Rabort Rtype_error))
                                             end
                          | res => res
                          end
                     else (st, Rerr (Rabort Rtype_error))
      | EVar n => match nsLookup n (sev env) with
                | Some v' => (st, Rval [v'])
                | None => (st, Rerr (Rabort Rtype_error))
                end
      | EFun x e => (st, Rval [Closure env x e])

      | EApp op es => match (evaluate st env (rev es)) with
                     | (st', Rval vs) => If op = Opapp
                                        then match do_opapp (rev vs) with
                                             | Some (env', e) =>
                                               if Peano_dec.eq_nat_dec (clock st') 0
                                               then (st', Rerr (Rabort Rtimeout_error))
                                               else evaluate (dec_clock st') env' [e]
                                             | None => (st', Rerr (Rabort Rtype_error))
                                             end
                                        else match do_app _ (refs st', ffi st') op (rev vs) with
                                             | Some ((refs, ffi), r) => ({| refs := refs;
                                                                           ffi  := ffi;
                                                                           clock := clock st';
                                                                           next_type_stamp := next_type_stamp st' ;
                                                                           next_exn_stamp := next_exn_stamp st'
                                                                        |},
                                                                        list_result r)
                                             | None => (st', Rerr (Rabort Rtype_error))
                                             end
                     | res => res
                     end

      | ELog lop e1 e2 => match (evaluate st env [e1]) with
                         | (st', Rval (v1::vs1)) => match do_log lop v1 e2 with
                                                  | Some (Exp e) => evaluate st' env [e]
                                                  | Some (Val v') => (st', Rval [v'])
                                                  | None => (st', Rerr (Rabort Rtype_error))
                                                  end
                         | res => res
                         end

      | EIf e1 e2 e3 => match (evaluate st env [e1]) with
                       | (st', Rval (v'::vs')) => match do_if v' e2 e3 with
                                                | Some e => evaluate st' env [e]
                                                | None => (st', Rerr (Rabort Rtype_error))
                                                end
                       | res => res
                       end

      | EMat e pes => match (evaluate st env [e]) with
                     | (st', Rval (v'::vs')) => evaluate_match st' env v' pes bind_exn_v
                     | res => res
                     end

      | ELet xo e1 e2 => match (evaluate st env [e1]) with
                        | (st', Rval (v'::vs')) => evaluate st'
                                {| sev := nsOptBind xo v' (sev env); sec := (sec env) |} [e2]
                        | res => res
                        end

      | ELetrec funs e => If LibList.noduplicates (map (fun trip => match trip with (x, y, z) => x end) funs)
                         then evaluate st {| sev := build_rec_env funs env (sev env); sec := (sec env) |} [e]
                         else (st, Rerr (Rabort Rtype_error))

      | ETannot e t => evaluate st env [e]
      | ELannot e l => evaluate st env [e]
      end
  in

  match es with
  | [] => (st, Rval [])
  | e'::es' => match evaluate_single_exp st env e' with
             | (st', Rval (v'::vs')) =>
               match evaluate st' env es' with
               | (st'', Rval vs'') => (st'', Rval (v'::vs''))
               | res => res
               end
             | res => res
             end
  end.
