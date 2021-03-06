Require Import CakeSem.Utils.
Require Import CakeSem.ffi.FFI.
Require Import CakeSem.Namespace.
Require Import CakeSem.CakeAST.
Require Import CakeSem.FreeVars.
Require Import CakeSem.SemanticsAux.

Require Import PeanoNat.
Require Import List.
Require Import ListDec.
Require Import Ascii.
Import Peano_dec.
Import ZArith_dec.
Import ListNotations.

Require Import Omega.

(* ---------------------------------------------------------------------- *)
(** ** Helper functions *)
Definition ident_string_dec := ident_eq_dec _ _ string_dec string_dec.

(* ---------------------------------------------------------------------- *)
(** ** Store assign *)
Fixpoint store_assign {A : Type} (n : nat) (v : store_v A) (st : store A) : option (store A) :=
  match List.nth_error st n with
  | Some v' => if store_v_same_type v' v
              then Some (update n v st)
              else None
  | _ => None
  end.

(* ---------------------------------------------------------------------- *)
(** ** Constructor comparison *)

Definition same_ctor (s1 s2 : stamp) : bool :=
  if stamp_eq_dec s1 s2 then true else false.


(* ---------------------------------------------------------------------- *)
(** ** Constructor construction *)

Definition build_conv (envC : env_ctor) (cn : constr_id) (vs : list val) : option val :=
  match cn with
  | None => Some (Conv None vs)
  | Some id => match nsLookup ident_string_dec id envC with
              | None => None
              | Some (len,stamp) => Some (Conv (Some stamp) vs)
              end
  end.

(* ---------------------------------------------------------------------- *)
(** ** Pattern matcher *)


(* A big-step pattern matcher.  If the value matches the pattern, return an
 * environment with the pattern variables bound to the corresponding sub-terms
 * of the value; this environment extends the environment given as an argument.
 * No_match is returned when there is no match, but any constructors
 * encountered in determining the match failure are applied to the correct
 * number of arguments, and constructors in corresponding positions in the
 * pattern and value come from the same type.  Match_type_error is returned
 * when one of these conditions is violated *)
Fixpoint pmatch (envC : env_ctor) (s : store val) (p : pat) (v : val)
         (env : alist varN val) : match_result (alist varN val) :=
  let fix pmatch_list (envC : env_ctor) (s : store val) (ps : list pat)
          (vs : list val) (env : alist varN val ) : match_result (alist varN val) :=
      match ps, vs with
      | [], [] => Match env
      | p::ps', v'::vs' =>
        (* Another way to do it (I THINK?) *)
        (* match pmatch envC s p v' env as res with
         * | Match env' => pmatch_list envC s ps' vs' env'
         * | _ => res
         * end *)
        match pmatch envC s p v' env with
        | No_match => No_match
        | Match_type_error => Match_type_error
        | Match env' => pmatch_list envC s ps' vs' env'
        end
      | _, _ => Match_type_error
      end
  in
  match p, v with
  | Pany, v' => Match env
  | Pvar x, v' => Match ((x,v')::env)
  | Plit l, Litv l' => if lit_eq_dec l l'
                      then Match env
                      else if lit_same_type l l'
                           then No_match
                           else Match_type_error
  | Pcon (Some n) ps, Conv (Some stamp') vs =>
    match  nsLookup ident_string_dec n envC with
    | Some (l, stamp) =>  if same_ctor stamp stamp'
                         then if eq_nat_dec (length ps) l (* TODO: suspicious redundant test *)
                              then pmatch_list envC s ps vs env
                              else Match_type_error
                         else No_match
    | _ => Match_type_error
    end
  | Pcon None ps, Conv None vs => pmatch_list envC s ps vs env
  (* I think this is just as fast? Actually...
   * maybe not though due to extra stuff happening on matches *)
  (* ORIG: *)
  (* if eqb (length ps) (length vs) *)
  (* then pmatch_list envC s ps vs env *)
  (* else Match_type_error *)
  | Pref p, Loc lnum => match store_lookup lnum s with
                       | Some (Refv v) => pmatch envC s p v env
                       | Some _ => Match_type_error
                       | None => Match_type_error
                       end
  | Ptannot p t, val' => pmatch envC s p val' env
  | _, _ => Match_type_error
  end.


(* ---------------------------------------------------------------------- *)
(** ** Typechecks *)

Definition do_con_check (cenv : env_ctor)
           (n_opt : constr_id)
           (l : nat) : bool := (* LATER: switch to Prop *)
  match n_opt with
  | None => true
  | Some n => match nsLookup ident_string_dec n cenv with
             | None => false
             | Some (l',_) => if Nat.eqb l l' then true else false
             end
  end.


(* ---------------------------------------------------------------------- *)
(** ** Equality test *)

Inductive eq_result : Type :=
| Eq_val : bool -> eq_result
| Eq_type_error.
Import Sumbool.

(* Here we can probably start Prop-ertizing *) (* LATER: ask about it *)
Fixpoint do_eq (e1 e2 : val) : eq_result :=
  let fix do_eq_list (el1 el2 : list val) : eq_result :=
      match el1, el2 with
      | [], [] => Eq_val true
      | v1::vs1, v2::vs2 => match do_eq v1 v2 with
                         | Eq_type_error => Eq_type_error
                         | Eq_val r => if negb r (* Why? *)
                                      then Eq_val false
                                      else do_eq_list vs1 vs2
                         end
      | _, _ => Eq_val false
      end
  in
  match e1, e2 with
  | Litv l1, Litv l2 => if lit_same_type l1 l2
                       then Eq_val (proj1_sig (bool_of_sumbool (lit_eq_dec l1 l2)))
                       else Eq_type_error
  | Loc l1, Loc l2 => Eq_val (Nat.eqb l1 l2)
  | Conv cn1 vs1, Conv cn2 vs2 => if sumbool_and _ _ _ _ (option_eq_dec stamp stamp_eq_dec cn1 cn2) (eq_nat_dec (length vs1) (length vs2))
                                 then do_eq_list vs1 vs2
                                 else if ctor_same_type cn1 cn2
                                      then Eq_val false
                                      else Eq_type_error
  | Vectorv vs1, Vectorv vs2 => if eq_nat_dec (length vs1) (length vs2)
                               then do_eq_list vs1 vs2
                               else Eq_val false
  | Closure _ _ _, Closure _ _ _ => Eq_val true
  | Closure _ _ _, Recclosure _ _ _ => Eq_val true
  | Recclosure _ _ _, Closure _ _ _ => Eq_val true
  | Recclosure _ _ _, Recclosure _ _ _ => Eq_val true
  | _, _ => Eq_type_error
  end.

(* ---------------------------------------------------------------------- *)
(** ** Function call *)

(* BACKPORT: the variable [n] should not be rebound, it's very confusing;
   the first one should be [nfun], the second one [narg] or just [n], but
   named in a consistant way with the non-recursive closure case. *)
(* LATER: not needed in the relational bigstep *)


Fixpoint do_opapp (vs : list val) : option (sem_env val * exp) :=
  match vs with
  | (Closure env n e)::v::[] =>
    Some (update_sev env (nsBind n v (sev env)), e)
  | (Recclosure env funs n)::v::[] =>
    if NoDuplicates_dec String.string_dec
                 (List.map (fun p => match p with (f,x,e) => f end) funs)
    then match find_recfun n funs with
         | Some (n,e) =>
            let sev' := nsBind n v (build_rec_env funs env (sev env)) in
            Some (update_sev env sev', e)
         | None => None
         end
    else None
  | _ => None
  end.

(* ---------------------------------------------------------------------- *)
(** ** Primitive function call *)

Definition store_ffi (ffi' : Type) (V : Type) := (store V * ffi_state ffi')%type.

Definition natFromInteger (size : nat) :=
      let fix helper (n' : nat ) (z : Z) : nat :=
          match n' with
          | O => O
          | S n'' =>
            (2 ^ n' * (Z.to_nat (Zdigits.bit_value
                                            (Z.testbit (Z.of_nat n'') z)))
                          + (helper n'' z))
          end
      in helper size.

Definition word8FromInteger (i : Z) : word 8 := nat_to_word 8 (natFromInteger 8 i)%nat .
Definition word64FromInteger (i : Z) : word 64 :=  nat_to_word 64 (natFromInteger 64%nat i).

Fixpoint do_app (ffi' : Type) (st : store_ffi ffi' val) (o : op) (vs : list val)
  : option (store_ffi ffi' val * result val val) :=
  match st with
    (s, t) =>
    match o, vs with
    | ListAppend, [x1;x2] =>
      match val_to_list x1, val_to_list x2 with
      | Some xs, Some ys =>
        Some ((s,t), Rval (list_to_val (xs ++ ys)))
      | _, _ => None
      end
    | Opn o', [Litv (IntLit n1); Litv (IntLit n2)] =>
      if sumbool_and _ _ _ _ (Z.eq_dec n2 0) (sumbool_or _ _ _ _ (opn_eq_dec o' Divide) (opn_eq_dec o' Modulo))
        then Some ((s,t), Rerr (Rraise div_exn_v))
        else Some ((s,t), Rval (Litv (IntLit (opn_lookup o' n1 n2))))
    | Opb o', [Litv (IntLit n1); Litv (IntLit n2)] =>
      Some ((s,t), Rval (Boolv (opb_lookup o' n1 n2)))
    | Opw W8 o', [Litv (Word8Lit w1); Litv (Word8Lit w2)] =>
      Some ((s,t), Rval (Litv (Word8Lit (opw8_lookup o' w1 w2))))
    | Opw W64 o', [Litv (Word64Lit w1); Litv (Word64Lit w2)] =>
      Some ((s,t), Rval (Litv (Word64Lit (opw64_lookup o' w1 w2))))
    (* | FP_bop bop, [Litv (Word64Lit w1); Litv (Word64Lit w2)] => *)
    (*     Some ((s,t),Rval (Litv (Word64Lit (fp_bop bop w1 w2)))) *)
    (* | FP_uop uop, [Litv (Word64Lit w)] => *)
    (*   Some ((s,t),Rval (Litv (Word64Lit (fp_uop uop w)))) *)
    (* | FP_cmp cmp, [Litv (Word64Lit w1); Litv (Word64Lit w2)] => *)
    (*   Some ((s,t),Rval (Boolv (fp_cmp cmp w1 w2))) *)
    | Shift W8 o' n, [Litv (Word8Lit w)] =>
      Some ((s,t), Rval (Litv (Word8Lit (shift8_lookup o' w n))))
    | Shift W64 o' n, [Litv (Word64Lit w)] =>
      Some ((s,t), Rval (Litv (Word64Lit (shift64_lookup o' w n))))
    | Equality, [v1; v2] =>
      match do_eq v1 v2 with
      | Eq_type_error => None
      | Eq_val b => Some ((s,t), Rval (Boolv b))
      end
    | Opassign, [Loc lnum; v] =>
      match store_assign lnum (Refv v) s with
      | Some s' => Some ((s',t), Rval (Conv None []))
      | None => None
      end
    | Opref, [v] =>
      let (s',n) := store_alloc (Refv v) s in
      Some ((s',t), Rval (Loc n))
    | Opderef, [Loc n] =>
      match store_lookup n s with
      | Some (Refv v) => Some ((s,t), Rval v)
      | _ => None
      end
    | Aw8alloc, [Litv (IntLit n); Litv (Word8Lit w)] =>
      if (Z_lt_dec n 0)%Z then
        Some ((s,t), Rerr (Rraise sub_exn_v))
      else
        let (s',lnum) := store_alloc (W8array (List.repeat w (Z.to_nat n))) s
        in Some ((s',t), Rval (Loc lnum))
    | Aw8sub, [Loc lnum; Litv (IntLit i)] =>
      match store_lookup lnum s with
      | Some (W8array ws) =>
        if (Z_lt_dec i 0)%Z
        then Some ((s,t), Rerr (Rraise sub_exn_v))
        else
          let n := Z.to_nat i in
          match List.nth_error ws n with
          | None => Some ((s,t), Rerr (Rraise sub_exn_v))
          | Some n' => Some ((s,t), Rval (Litv (Word8Lit n')))
          end
      | _ => None
      end
    | Aw8length, [Loc n] =>
      match store_lookup n s with
      | Some (W8array ws) => Some ((s,t), Rval (Litv (IntLit (ZArith.Zcomplements.Zlength ws))))
      | _ => None
      end
    | Aw8update, [Loc lnum; Litv (IntLit i); Litv (Word8Lit w)] =>
      match store_lookup lnum s with
      | Some (W8array ws) =>
        if (Z_lt_dec i 0)%Z then
          Some ((s,t), Rerr (Rraise sub_exn_v))
        else
          let n := Z.to_nat i in
          if Nat.leb (List.length ws) n then
            Some ((s,t), Rerr (Rraise sub_exn_v))
          else
            match store_assign lnum (W8array (update n w ws)) s with
            | None => None
            | Some s' => Some ((s',t), Rval (Conv None []))
            end
      | _ => None
      end
    | WordFromInt W8, [Litv (IntLit i)] =>
      Some ((s,t), Rval (Litv (Word8Lit (word8FromInteger i))))
    | WordFromInt W64, [Litv (IntLit i)] =>
      Some ((s,t), Rval (Litv (Word64Lit (word64FromInteger i))))
    | WordToInt W8, [Litv (Word8Lit w)] =>
      Some ((s,t), Rval (Litv (IntLit (Z.of_nat (word_to_nat _ w)))))
    | WordToInt W64, [Litv (Word64Lit w)] =>
      Some ((s,t), Rval (Litv (IntLit (Z.of_nat (word_to_nat _ w)))))
    | CopyStrStr, [Litv (StrLit str); Litv (IntLit off); Litv (IntLit len)] =>
      Some ((s,t),
            match copy_array (string_to_list_char str,off) len None with
            | None => Rerr (Rraise sub_exn_v)
            | Some cs => Rval (Litv (StrLit (list_char_to_string cs)))
            end)
    | CopyStrAw8, [Litv (StrLit str); Litv (IntLit off); Litv (IntLit len);
                     Loc dst; Litv (IntLit dstoff)] =>
      match store_lookup dst s with
      | Some (W8array ws) =>
        match copy_array (string_to_list_char str, off) len
                         (Some (map word8_to_char ws, dstoff)) with
        | None => Some ((s,t), Rerr (Rraise sub_exn_v))
        | Some cs =>
          match store_assign dst (W8array (map char_to_word8 cs)) s with
          | Some s' =>  Some ((s',t), Rval (Conv None []))
          | _ => None
          end
        end
      | _ => None
      end
    | CopyAw8Str, [Loc src; Litv (IntLit off); Litv (IntLit len)] =>
      match store_lookup src s with
      | Some (W8array ws) =>
        Some ((s,t),
        match copy_array (ws,off) len None with
        | None => Rerr (Rraise sub_exn_v)
        | Some ws => Rval (Litv (StrLit( list_char_to_string
                                         (map word8_to_char ws))))
        end)
      | _ => None
      end
    | CopyAw8Aw8, [Loc src; Litv (IntLit off); Litv (IntLit len);
                     Loc dst; Litv (IntLit dstoff)] =>
      match store_lookup src s, store_lookup dst s with
      | Some (W8array ws), Some (W8array ds) =>
        match copy_array (ws,off) len (Some (ds,dstoff)) with
        | None => Some ((s,t), Rerr (Rraise sub_exn_v))
        | Some ws =>
          match store_assign dst (W8array ws) s with
          | Some s' => Some ((s',t), Rval (Conv None []))
          | _ => None
          end
        end
      | _, _ => None
      end
    | Ord, [Litv (CharLit c)] =>
      Some ((s,t), Rval (Litv (IntLit (Z.of_nat (nat_of_ascii c)))))
    | Chr, [Litv (IntLit i)] =>
      Some ((s,t), if sumbool_and _ _ _ _ (Z_lt_dec i 0)%Z (Z_lt_dec 255 i)%Z
                   then Rerr (Rraise chr_exn_v)
                   else Rval (Litv (CharLit (ascii_of_nat (Z.to_nat i)))))
    | Chopb op, [Litv (CharLit c1); Litv (CharLit c2)] =>
      Some ((s,t), Rval (Boolv (opb_lookup op (Z.of_nat (nat_of_ascii c1))
                                           (Z.of_nat (nat_of_ascii c2)))))
    | Implode, [v] =>
      match val_to_char_list v with
      | Some ls => Some ((s,t), Rval (Litv (StrLit (list_char_to_string ls))))
      | None => None
      end
    | Strsub, [Litv (StrLit str); Litv (IntLit i)] =>
      if (Z_lt_dec i 0)%Z then
        Some ((s,t), Rerr (Rraise sub_exn_v))
      else
        let n := Z.to_nat i in
        match String.get n str with
        | Some n' => Some ((s,t), Rval (Litv (CharLit n')))
        | None    => Some ((s,t), Rerr (Rraise sub_exn_v))
        end
    | StrLen, [Litv (StrLit str)] =>
      Some ((s,t), Rval (Litv (IntLit (Z.of_nat (String.length str)))))
    | Strcat, [v] =>
      match val_to_list v with
      | Some vs =>
        match vals_to_string vs with
        | Some str =>
          Some ((s,t), Rval (Litv(StrLit str)))
        | _ => None
        end
      | _ => None
      end
    | VfromList, [v] =>
      match val_to_list v with
      | Some vs => Some ((s,t), Rval (Vectorv vs))
      | None    => None
      end
    | VSub, [Vectorv vs; Litv (IntLit i)] =>
      if (Z_lt_dec i 0)%Z
      then Some ((s,t), Rerr (Rraise sub_exn_v))
      else
        let n := Z.to_nat i in
        match nth_error vs n with
        | None    => Some ((s,t), Rerr (Rraise sub_exn_v))
        | Some v' => Some ((s,t), Rval v')
        end
    | Vlength, [Vectorv vs] =>
      Some ((s,t), Rval (Litv (IntLit (Z.of_nat (List.length  vs)))))
    | Aalloc, [Litv (IntLit n); v] =>
      if (Z_lt_dec n 0)%Z
      then Some ((s,t), Rerr (Rraise sub_exn_v))
      else
        let (s',lnum) := store_alloc (Varray (List.repeat v (Z.to_nat n))) s
        in Some ((s',t), Rval (Loc lnum))
    | AallocEmpty, [Conv None []] =>
      let (s',lnum) := store_alloc (Varray []) s
      in Some ((s',t), Rval (Loc lnum))
    | Asub, [Loc lnum; Litv (IntLit i)] =>
      match store_lookup lnum s with
      | Some (Varray vs) =>
        if (Z_lt_dec i 0)%Z then
          Some ((s,t), Rerr (Rraise sub_exn_v))
        else
          let n := Z.to_nat i in
          match nth_error vs n with
          | None    => Some ((s,t), Rerr (Rraise sub_exn_v))
          | Some v' => Some ((s,t), Rval v')
          end
      | _ => None
      end
    | Alength, [Loc n] =>
      match store_lookup n s with
      | Some (Varray ws) =>
        Some ((s,t), Rval (Litv (IntLit (Z.of_nat (List.length ws)))))
      | _ => None
      end
    | Aupdate, [Loc lnum; Litv (IntLit i); v] =>
      match store_lookup lnum s with
      | Some (Varray vs') =>
        if (Z_lt_dec i 0)%Z then (* LATER: use a wrapper function for this kind of test *)
          Some ((s,t), Rerr (Rraise sub_exn_v))
        else
          let n := Z.to_nat i in
          if Nat.leb (List.length vs') n
          then Some ((s,t), Rerr (Rraise sub_exn_v))
          else
            match store_assign lnum (Varray (update n v vs')) s with
            | None => None
            | Some s' => Some ((s',t), Rval (Conv None []))
            end
      | _ => None
      end
    | ConfigGC, [Litv (IntLit i); Litv (IntLit j)] =>
      Some ((s,t), Rval (Conv None []))
    | FFI n, [Litv(StrLit conf); Loc lnum] =>
      match store_lookup lnum s with
      | Some (W8array ws) =>
        match call_FFI t n (List.map (fun c' => nat_to_word 8 (nat_of_ascii c'))
                                     (string_to_list_char conf)) ws with
        | Ffi_return _ t' ws' =>
          match store_assign lnum (W8array ws') s with
          | Some s' => Some ((s', t'), Rval (Conv None []))
          | None => None
          end
        | Ffi_final _ outcome =>
          Some ((s, t), Rerr (Rabort (Rffi_error outcome)))
        end
      | _ => None
      end
    | _, _ => None
    end
  end.

Inductive exp_or_val : Type :=
  | Exp : exp -> exp_or_val
  | Val : val -> exp_or_val.

Definition do_log (op : lop) (v : val) (e : exp) : option exp_or_val :=
  match op with (* LATER: would be more idiomatic to write "If v = Boolv true" *)
  | And => if val_eq_dec (Boolv true) v
          then Some (Exp e)
          else if val_eq_dec (Boolv false) v
               then Some (Val v)
               else None

  | Or => if val_eq_dec (Boolv true) v
          then Some (Val v)
          else if val_eq_dec (Boolv false) v
               then Some (Exp e)
               else None
  end.

Definition do_if (v : val) (e1 e2 : exp) : option exp :=
  if val_eq_dec (Boolv true) v
    then Some e1
    else if val_eq_dec (Boolv false) v
         then Some e2
         else None.

(* ---------------------------------------------------------------------- *)

Definition list_result {A B : Type} (res : result A B) : result (list A) B :=
  match res with
  | Rval v => Rval [v]
  | Rerr e => Rerr e
  end.

Fixpoint evaluate (fuel : nat) {ffi' : Type} (st : state ffi') (env : sem_env val)
         (es : list exp) : state ffi' * result (list val) val :=
  match fuel with
  | O => (st, Rerr (Rabort Rtimeout_error))
  | S fuel' =>
    let fix evaluate_match (st : state ffi') (env : sem_env val) (v' : val)
            (pes : list (pat * exp)) (err_v : val) : state ffi' * result (list val) val :=
        match pes with
        | [] => (st, Rerr (Rraise err_v))
        | (p,e)::pes' => if NoDuplicates_dec string_dec (pat_bindings p)
                       then match pmatch (sec env) (refs st) p v' [] with
                            | Match env_v' => evaluate fuel' st {| sev := nsAppend (alist_to_ns env_v') (sev env);
                                                                  sec := (sec env) |} [e]
                            | No_match => evaluate_match st env v' pes' err_v
                            | Match_type_error => (st, Rerr (Rabort Rtype_error))
                            end
                       else (st, Rerr (Rabort Rtype_error))
        end
    in

    let fix evaluate_single_exp (st : state ffi') (env : sem_env val) (ex : exp)
        : state ffi' * result (list val) val :=
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
                        then match evaluate fuel' st env (rev es') with
                             | (st', Rval vs) => match build_conv (sec env) cn (rev vs) with
                                                | Some v' => (st', Rval [v'])
                                                | None => (st', Rerr (Rabort Rtype_error))
                                                end
                             | res => res
                             end
                        else (st, Rerr (Rabort Rtype_error))
        | EVar n => match nsLookup ident_string_dec n (sev env) with
                   | Some v' => (st, Rval [v'])
                   | None => (st, Rerr (Rabort Rtype_error))
                   end
        | EFun x e => (st, Rval [Closure env x e])

        | EApp op es => match (evaluate fuel' st env (rev es)) with
                       | (st', Rval vs) => if op_eq_dec op Opapp
                                          then match do_opapp (rev vs) with
                                               | Some (env', e) => evaluate fuel' st' env' [e]
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

        | ELog lop e1 e2 => match (evaluate fuel' st env [e1]) with
                           | (st', Rval (v1::vs1)) => match do_log lop v1 e2 with
                                                    | Some (Exp e) => evaluate fuel' st' env [e]
                                                    | Some (Val v') => (st', Rval [v'])
                                                    | None => (st', Rerr (Rabort Rtype_error))
                                                    end
                           | res => res
                           end

        | EIf e1 e2 e3 => match (evaluate fuel' st env [e1]) with
                         | (st', Rval (v'::vs')) => match do_if v' e2 e3 with
                                                  | Some e => evaluate fuel' st' env [e]
                                                  | None => (st', Rerr (Rabort Rtype_error))
                                                  end
                         | res => res
                         end

        | EMat e pes => match (evaluate fuel' st env [e]) with
                       | (st', Rval (v'::vs')) => evaluate_match st' env v' pes bind_exn_v
                       | res => res
                       end

        | ELet xo e1 e2 => match (evaluate fuel' st env [e1]) with
                          | (st', Rval (v'::vs')) => evaluate fuel' st'
                                                            {| sev := nsOptBind xo v' (sev env); sec := (sec env) |} [e2]
                          | res => res
                          end

        | ELetrec funs e =>  if NoDuplicates_dec (pair_eq_dec _ _ (pair_eq_dec _ _ string_dec string_dec) exp_eq_dec) funs
                            then evaluate fuel' st {| sev := build_rec_env funs env (sev env); sec := (sec env) |} [e]
                            else (st, Rerr (Rabort Rtype_error))

        | ETannot e t => evaluate fuel' st env [e]
        | ELannot e l => evaluate fuel' st env [e]
        end
    in

    match es with
    | [] => (st, Rval [])
    | e'::es' => match evaluate_single_exp st env e' with
               | (st', Rval (v'::vs')) =>
                 match evaluate fuel' st' env es' with
                 | (st'', Rval vs'') => (st'', Rval (v'::vs''))
                 | res => res
                 end
               | res => res
               end
    end
  end.

Fixpoint identity_to_string (i : ident modN varN) : string :=
  match i with
  | Short n => n
  | Long m i' => m ++ (identity_to_string i')
  end.

Fixpoint evaluate_opt {ffi' : Type} (st : state ffi') (env : sem_env val)
         (es : list exp) (fuel : nat) : state ffi' * result (list val) val :=
  match fuel with
  | O => (st, Rerr (Rabort Rtimeout_error))
  | S fuel' =>
    let fix evaluate_match (st : state ffi') (env : sem_env val) (v' : val)
            (pes : list (pat * exp)) (err_v : val) : state ffi' * result (list val) val :=
        match pes with
        | [] => (st, Rerr (Rraise err_v))
        | (p,e)::pes' => if NoDuplicates_dec string_dec (pat_bindings p)
                       then match pmatch (sec env) (refs st) p v' [] with
                            | Match env_v' => (evaluate_opt st {| sev := nsAppend (alist_to_ns env_v') (sev env);
                                                                 sec := (sec env) |} [e] fuel')
                            | No_match => evaluate_match st env v' pes' err_v
                            | Match_type_error => (st, Rerr (Rabort Rtype_error))
                            end
                       else (st, Rerr (Rabort Rtype_error))
        end
    in

    let fix evaluate_single_exp (st : state ffi') (env : sem_env val) (ex : exp)
        : state ffi' * result (list val) val :=
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
                        then match (evaluate_opt st env (rev es') fuel') with
                             | (st', Rval vs) => match build_conv (sec env) cn (rev vs) with
                                                | Some v' => (st', Rval [v'])
                                                | None => (st', Rerr (Rabort Rtype_error))
                                                end
                             | res => res
                             end
                        else (st, Rerr (Rabort Rtype_error))
        | EVar n => match nsLookup ident_string_dec n (sev env) with
                   | Some v' => (st, Rval [v'])
                   | None => (st, Rerr (Rabort Rtype_error))
                   end
        | EFun x e => (st, Rval [Closure (optimize_sem_env env (free_vars e)) x e])

        | EApp op es => match (evaluate_opt st env (rev es) fuel') with
                       | (st', Rval vs) =>
                         if op_eq_dec op Opapp
                         then match do_opapp (rev vs) with
                              | Some (env', e) => (evaluate_opt st' env' [e] fuel')
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

        | ELog lop e1 e2 => match (evaluate_opt st env [e1] fuel') with
                           | (st', Rval (v1::vs1)) => match do_log lop v1 e2 with
                                                    | Some (Exp e) => (evaluate_opt st' env [e] fuel')
                                                    | Some (Val v') => (st', Rval [v'])
                                                    | None => (st', Rerr (Rabort Rtype_error))
                                                    end
                           | res => res
                           end

        | EIf e1 e2 e3 => match (evaluate_opt st env [e1] fuel') with
                         | (st', Rval (v'::vs')) => match do_if v' e2 e3 with
                                                  | Some e => (evaluate_opt st' env [e] fuel')
                                                  | None => (st', Rerr (Rabort Rtype_error))
                                                  end
                         | res => res
                         end

        | EMat e pes => match (evaluate_opt st env [e] fuel') with
                       | (st', Rval (v'::vs')) => evaluate_match st' env v' pes bind_exn_v
                       | res => res
                       end

        | ELet xo e1 e2 => match (evaluate_opt st env [e1] fuel') with
                          | (st', Rval (v'::vs')) => (evaluate_opt st'
                                                                 {| sev := nsOptBind xo v' (sev env); sec := (sec env) |} [e2] fuel')
                          | res => res
                          end

        | ELetrec funs e =>  if NoDuplicates_dec (pair_eq_dec _ _ (pair_eq_dec _ _ string_dec string_dec) exp_eq_dec) funs
                            then (evaluate_opt st {| sev := build_rec_env funs env (sev env); sec := (sec env) |} [e] fuel')
                            else (st, Rerr (Rabort Rtype_error))

        | ETannot e t => (evaluate_opt st env [e] fuel')
        | ELannot e l => (evaluate_opt st env [e] fuel')
        end
    in

    match es with
    | [] => (st, Rval [])
    | e'::es' => match evaluate_single_exp st env e' with
               | (st', Rval (v'::vs')) =>
                 match (evaluate_opt st' env es' fuel') with
                 | (st'', Rval vs'') => (st'', Rval (v'::vs''))
                 | res => res
                 end
               | res => res
               end
    end
  end.

Fixpoint size_exp (e : exp) : nat :=
  let fix size_exps (es : list exp) :=
      match es with
      | [] => 0
      | e'::es => size_exp e' + size_exps es
      end
  in
  match e with
  | ELit _ | EVar _ => 1
  | EFun _ e'    | ERaise e'
  | EHandle e' _ | EMat e' _
  | ELetrec _ e' | ETannot e' _
  | ELannot e' _ => 1 + size_exp e'
  | ECon _ es | EApp _ es => 1 + size_exps es
  | ELet _ e' e'' | ELog _ e' e'' => 1 + size_exp e' + size_exp e''
  | EIf  e' e'' e''' => 1 + size_exp e' + size_exp e'' + size_exp e'''
  end.

Definition size_exps (es : list exp) : nat := fold_left plus (map size_exp es) O.

Fixpoint size_dec (d : dec) : nat :=
  match d with
  | Dlet _ _ _ => 1
  | Dletrec _ _ => 1
  | Dtype _ _ => 1
  | Dtabbrev _ _ _ _ => 1
  | Dexn _ _ _ => 1
  | Dmod _ ds => 1 + fold_left plus (List.map size_dec ds) O
  | Dlocal lds ds => 1 + fold_left plus (List.map size_dec ds) O + fold_left plus (List.map size_dec lds) O
  end.

Definition size_decs (ds : list dec) : nat := fold_left plus (map size_dec ds) O.

Lemma size_dec_min_1 : forall (d : dec), 1 <= size_dec d.
Proof.
 destruct d; simpl; omega.
Qed.

Program Fixpoint evaluate_decs {ffi' : Type} (fuel : nat) (st : state ffi') (env : sem_env val) (decl : list dec) {measure (size_decs decl)}:
  (state ffi' * result (sem_env val) val) :=
  let fuel' := fuel in
  (* match fuel with *)
  (* | O => (st, Rerr (Rabort Rtimeout_error)) *)
  (* | S fuel' => *)
    match decl with
    | [] => (st, Rval empty_sem_env)
    | d1::d2::decl' => match evaluate_decs fuel' st env [d1] with
                    | (st1, Rval env1) =>
                      match evaluate_decs fuel' st1 (extend_dec_env env1 env) (d2::decl') with
                      | (st2, r) => (st2, combine_dec_result env1 r)
                      end
                    | res => res
                    end

    | [Dlet locs p e] =>
      if NoDuplicates_dec string_dec (pat_bindings p)
      then match evaluate_opt st env [e] fuel with
           | (st', Rval v) =>
             (st', match pmatch (sec env) (refs st') p (hd (Litv (StrLit "IF HERE THEN BAD")) v) [] with
                   | Match new_vals => Rval {| sec := nsEmpty; sev := alist_to_ns new_vals |}
                   | No_match => Rerr (Rraise bind_exn_v)
                   | Match_type_error => Rerr (Rabort Rtype_error)
                   end)
           | (st', Rerr err) => (st', Rerr err)
           end
      else (st, Rerr (Rabort Rtype_error))

    | [Dletrec locs funs] => (st,
                             if NoDuplicates_dec string_dec (map (fun x => fst (fst x)) funs)
                             then Rval {| sev := build_rec_env funs env nsEmpty; sec := nsEmpty |}
                             else Rerr (Rabort Rtype_error))

    | [Dtype locs tds] => if UniqueCtorsInDefs_dec tds
                         then (state_update_next_type_stamp st (next_type_stamp st + List.length tds),
                               Rval {| sev := nsEmpty; sec := build_tdefs (next_type_stamp st) tds |})
                         else (st, Rerr (Rabort Rtype_error))
    | [Dtabbrev locs tvs tn t] => (st, Rval {| sev := nsEmpty; sec := nsEmpty |})
    | [Dexn locs cn ts] => (state_update_next_exn_stamp st (next_exn_stamp st + 1),
                           Rval {| sev := nsEmpty;
                                   sec := nsSing cn (List.length ts, ExnStamp (next_exn_stamp st)) |})
    | [Dmod mn ds] => match evaluate_decs fuel' st env ds with
                     | (st', r) => (st',
                                   match r with
                                   | Rval env' => Rval {| sev := nsLift mn (sev env');
                                                         sec := nsLift mn (sec env') |}
                                   | Rerr err => Rerr err
                                   end)
                     end
    | [Dlocal lds ds] => match evaluate_decs fuel' st env lds with
                        | (st1, Rval env1) =>
                          evaluate_decs fuel' st1 (extend_dec_env env1 env) ds
                        | res => res
                        end
    end.
Obligation 1.
unfold size_decs. simpl.

assert (fold_addition_lt : forall (l : list nat) (n m : nat), n < m -> n < fold_left plus l m).
    (induction l; intros n m H; try (specialize (IHl n (m+a))); simpl; omega).

pose size_dec_min_1 as H.

destruct d1; simpl;
try (apply fold_addition_lt;
specialize (size_dec_min_1 d2); omega).
Qed.
Obligation 2.
unfold size_decs. simpl.
assert (fold_addition_lt : forall (l : list nat) (m n : nat), m < m + n -> fold_left plus l m < fold_left plus l (m + n)).
induction l; intros m n H.
simpl; omega.
simpl. rewrite <- (plus_assoc m n a). rewrite (plus_comm n a). rewrite (plus_assoc m a n).
apply IHl. omega.

rewrite plus_comm.
apply fold_addition_lt.
specialize (size_dec_min_1 d2).
specialize (size_dec_min_1 d1).
omega.
Qed.
Obligation 5.
unfold size_decs.
simpl. omega.
Qed.
Obligation 6.
unfold size_decs. simpl. omega.
Qed.
