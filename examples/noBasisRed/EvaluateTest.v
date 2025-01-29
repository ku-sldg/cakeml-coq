Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Require Import StructTact.StructTactics.

Require Import CakeSem.Utils.
Require Import FFI.
Require Import CakeSem.Namespace.
Require Import CakeSem.CakeAST.
Require Import CakeSem.SemanticsAux.
Require Import CakeSem.Evaluate.

Require Import NoBasis.


Definition init_env : sem_env val := empty_sem_env.
Definition init_store := empty_store val.

Parameter A : Type.
Parameter init_ffi_st : ffi_state A.
Definition init_state := Build_state 0 init_store init_ffi_st 0 0.

Definition noBasisProg := evaluate_decs 100 init_state init_env [ dec_def_0
                                                                ; dec_def_1
                                                                ; dec_def_2
                                                                ; dec_def_3
                                                                ; dec_def_4
                                                                ].

Definition noBasisProg' := evaluate_decs 19 init_state init_env [ dec_def_0
                                                                ; dec_def_1
                                                                ; dec_def_2
                                                                ; dec_def_3
                                                                ; dec_def_4
                                                                ].

(* Opaque evaluate_opt. *)
(* Opaque evaluate_decs. *)

Eval cbv in noBasisProg.

Definition my_env :=
  {| sev := [(Short "answer",
              Conv (Some (TypeStamp "S" 0))
                   [Conv (Some (TypeStamp "S" 0))
                         [Conv (Some (TypeStamp "S" 0))
                               [Conv (Some (TypeStamp "S" 0))
                                     [Conv (Some (TypeStamp "S" 0)) [Conv (Some (TypeStamp "O" 0)) []]]]]]);
               (Short "three",
                Conv (Some (TypeStamp "S" 0))
                     [Conv (Some (TypeStamp "S" 0))
                           [Conv (Some (TypeStamp "S" 0)) [Conv (Some (TypeStamp "O" 0)) []]]]);
               (Short "two",
                Conv (Some (TypeStamp "S" 0)) [Conv (Some (TypeStamp "S" 0)) [Conv (Some (TypeStamp "O" 0)) []]]);
               (Short "plus",
                Recclosure
                  {| sev := []; sec := [(Short "S", (1, TypeStamp "S" 0)); (Short "O", (0, TypeStamp "O" 0))] |}
                  [("plus", "x",
                    EFun "y"
                         (ELannot
                            (EMat (ELannot (EVar (Short "x")) [0])
                                  [(Pcon (Some (Short "O")) [], ELannot (EVar (Short "y")) [0]);
                                     (Pcon (Some (Short "S")) [Pvar "xp"],
                                      ELannot
                                        (ECon (Some (Short "S"))
                                              [EApp Opapp
                                                    [ELannot
                                                       (EApp Opapp
                                                             [ELannot (EVar (Short "plus")) [0]; ELannot (EVar (Short "xp")) [0]])
                                                       [0]; ELannot (EVar (Short "y")) [0]]]) [0])]) [0]))] "plus")];
     sec := [(Short "S", (1, TypeStamp "S" 0)); (Short "O", (0, TypeStamp "O" 0))] |}.

Definition my_st := {| clock := 0; refs := []; ffi := init_ffi_st; next_type_stamp := 1; next_exn_stamp := 0 |}.

Inductive nat_rel_cake_nat (typestamp : nat) : nat -> val -> Prop :=
| zero_rel : nat_rel_cake_nat typestamp 0 (Conv (Some (TypeStamp "O" typestamp)) [])
| suc_rel  : forall (n : nat) (prev : val), nat_rel_cake_nat typestamp n prev -> nat_rel_cake_nat typestamp (S n) (Conv (Some (TypeStamp "S" typestamp)) [prev]).

Check nat_rel_cake_nat_ind.
Print nat_rel_cake_nat_ind.


Fixpoint nat_to_cake_nat (typestamp : nat) (n : nat) : val :=
  match n with
  | O => (Conv (Some (TypeStamp "O" typestamp)) [])
  | S n' => (Conv (Some (TypeStamp "S" typestamp)) [nat_to_cake_nat typestamp n'])
  end.

Lemma nat_to_cake_nat_rel : forall (typestamp n : nat), nat_rel_cake_nat typestamp n (nat_to_cake_nat typestamp n).
Proof.
  induction n; simpl; constructor; assumption.
Qed.

Ltac step_fuel_in fuel H := destruct fuel; simpl in H.

Definition evaluate_diverges {ffi' : Type} (st : state ffi') (env : sem_env val) (e : exp) : Prop :=
  forall (fuel : nat), exists (st' : state ffi'), evaluate fuel st env [e] = (st', Rerr (Rabort Rtimeout_error)).

(* Opaque evaluate. *)
Lemma exists_fuel_no_divergence : forall (st : state A) (env : sem_env val) (e : exp) (v : val),
    (exists (f : nat), evaluate f st env [e] = (st, Rval [v])) -> ~ evaluate_diverges st env e.
Proof.
  intros st env e.
  induction e;
    intros va H contra;
    inversion H as [f H']; specialize (contra f); inversion contra as [st' contra']; clear H; clear contra;
     rewrite H' in contra'; inversion contra'.
Qed.

Ltac inv H := inversion H; subst; clear H.
(* if an expression's subexpressions diverge then it diverges *)
(* Lemma divergence_subexpressions : forall (st : state A) (env : sem_env val) (e1 e2 : exp), *)
(*     evaluate_diverges st env e1 -> *)
(*     is_subexp e1 e2 -> *)
(*     evaluate_diverges st env e2. *)
(* Proof. *)
(*   intros st env e1 e2. generalize dependent e1. induction e2; intros e1 H1 H2. *)
(*   - inv X; inv H2. *)
(*     + assumption. *)
(*     + inv H3; inv H. *)
(*     + assumption. *)
(*     + inv H4; inv H0. *)
(*       * unfold evaluate_diverges. destruct fuel. *)
(*         -- exists st; reflexivity. *)
(*            Abort. *)

(* Lemma no_divergence_exists_fuel : forall (st : state A) (env : sem_env val) (e : exp), *)
(*     ~ evaluate_diverges st env e -> *)
(*     (exists (f : nat), (exists (v : val), evaluate f st env [e] = (st, Rval [v])) \/ *)
(*      (exists (a : abort), evaluate f st env [e] = (st, Rerr (Rabort a)))). *)
(* Proof. *)
(*   intros st env e H. *)
(*   induction e. *)
(*   - destruct X. *)
(*     + unfold evaluate_diverges in H. unfold constr_id in o. destruct o. *)
(*       * exists 2. unfold evaluate. *)
(*         destruct (do_con_check (sec env) (Some i) (@Datatypes.length exp [])). simpl. *)
(*         -- destruct (nsLookup ident_string_dec i (sec env)). destruct p. simpl. *)
(*            ++ left. exists (Conv (Some s) []). reflexivity. *)
(*            ++ right. exists Rtype_error. reflexivity. *)
(*         -- right. exists Rtype_error. reflexivity. *)
(*       * exists 2. simpl. left. exists (Conv None []). reflexivity. *)
(*     + Abort. *)

(* Lemma no_divergence_exists_fuel : forall (st : state A) (env : sem_env val) (e : exp), *)
(*     ~ evaluate_diverges st env e -> *)
(*     (exists (f : nat), (exists (v : val), evaluate f st env [e] = (st, Rval [v])) \/ *)
(*      (exists (a : abort), evaluate f st env [e] = (st, Rerr (Rabort a)) /\ a <> Rtimeout_error)). *)
(* Admitted. *)

(* Lemma inc_fuel_same_val : forall (f : nat) (st st' : state A) (env : sem_env val) (e : exp) (vs : list val), *)
(*     a = c -> *)
(*     b = c -> a = b. *)

(* Ltac things := *)
(*   match goal with *)
(*   | [|- context[evaluate (S ?f) _ _ _]] =>  *)
Lemma evaluate_single_step : forall (fuel' : nat) (st : state A) (env : sem_env val) (es : list exp),
    evaluate (S fuel') st env es =
    match es with
    | [] => (st, Rval [])
    | [EVar n] => match nsLookup ident_string_dec n (sev env) with
                 | Some v' => (st, Rval [v'])
                 | None => (st, Rerr (Rabort Rtype_error))
                 end
    | [EFun x e] => (st, Rval [Closure env x e])
    | [ECon cn es'] => if do_con_check (sec env) cn (length es')
                      then match evaluate fuel' st env (rev es') with
                           | (st', Rval vs) => match build_conv (sec env) cn (rev vs) with
                                              | Some v' => (st', Rval [v'])
                                              | None => (st', Rerr (Rabort Rtype_error))
                                              end
                           | res => res
                           end
                      else (st, Rerr (Rabort Rtype_error))

    | [EApp op es] => match (evaluate fuel' st env (rev es)) with
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

    | [EMat e pes] => match (evaluate fuel' st env [e]) with
                     | (st', Rval (v'::vs')) =>
                       (fix evaluate_match (st : state A) (env : sem_env val) (v' : val)
                            (pes : list (pat * exp)) (err_v : val) : state A * result (list val) val :=
                          match pes with
                          | [] => (st, Rerr (Rraise err_v))
                          | (p,e)::pes' =>
                            if NoDuplicates_dec string_dec (pat_bindings p)
                            then match pmatch (sec env) (refs st) p v' [] with
                                 | Match env_v' => evaluate fuel' st {| sev := nsAppend (alist_to_ns env_v') (sev env);
                                                                       sec := (sec env) |} [e]
                                 | No_match => evaluate_match st env v' pes' err_v
                                 | Match_type_error => (st, Rerr (Rabort Rtype_error))
                                 end
                            else (st, Rerr (Rabort Rtype_error))
                          end)
                         st' env v' pes bind_exn_v
                     | res => res
                     end

    | [ELannot e l] => evaluate fuel' st env [e]

    | e::es' => match evaluate fuel' st env [e] with
              | (st', Rval vs) => (* This differs from lem semantics*)
                match evaluate fuel' st' env es' with
                | (st'', Rval vs'') =>
                  match vs with
                  | [] => (st'', Rval vs'') (* This should never happen *)
                  | v::vs' => (st'', Rval (v::vs''))
                  end
                | res => res
                end
              | res => res
              end
    end.
Proof. reflexivity. Qed.

(* Lemma inc_fuel_same_val : forall (f : nat) (es : list exp) (st st' : state A) (env : sem_env val) (vs : list val), *)
(*     evaluate f st env es = (st', Rval vs) -> *)
(*     evaluate (S f) st env es = (st', Rval vs). *)
(* Proof. *)
(*   induction f. *)
(*   - intros es st st' env vs H. inv H. *)
(*   - induction es as [|e es']; *)
(*       intros st st' env vs H. *)
(*     + assumption. *)
(*     + rewrite evaluate_single_step. *)
(*       rewrite evaluate_single_step in H. *)
(*       destruct e. *)
(*       * destruct (do_con_check (sec env) c (Datatypes.length l)); *)
(*           destruct (evaluate f st env (rev l)) eqn:term0; *)
(*           destruct (evaluate f st env [ECon c l]) eqn:term1; *)
(*           destruct (evaluate f s0 env es') eqn:term2; *)
(*           destruct r; destruct r0; destruct r1; destruct es'; *)
(*             try( apply IHf in term0); *)
(*             try( apply IHf in term1); *)
(*             try( apply IHf in term2); *)
(*             try( rewrite term0); *)
(*             try( rewrite term1); *)
(*             try( rewrite term2); *)
(*             try( rewrite term2); try (assumption); try (inv H). *)
(*         destruct l1. auto. *)
(*         destruct l1. inv H1. auto. *)
(*         destruct l0. auto. *)
(*         destruct l0. inv H1. auto. *)
(*         destruct l1. auto. *)
(*         destruct l1. inv H1. auto. *)
(*         destruct l0. auto. *)
(*         destruct l0. inv H1. auto. *)
(*       * destruct es'; auto. *)
(*         destruct (evaluate f st env [EVar i]) eqn:term0. destruct r. *)
(*         try( apply IHf in term0). *)
(*         try( rewrite term0). *)
(*         destruct (evaluate f s env (e::es')) eqn:term1. destruct r. *)
(*         try( apply IHf in term1). *)
(*         try( rewrite term1). *)
(*         auto. *)
(*         destruct l; auto. *)
(*         destruct l; auto. *)
(*         inv H. *)
(*         inv H. *)
(*       * destruct es'; auto. *)
(*         destruct (evaluate f st env [EFun v e]) eqn:term0; *)
(*         destruct (evaluate f s env (e0 :: es')) eqn:term1; *)
(*         destruct r; destruct r0. *)
(*         apply IHf in term0. *)
(*         apply IHf in term1. *)
(*         rewrite term0. *)
(*         rewrite term1. *)
(*         auto. *)
(*         apply IHf in term0. *)
(*         rewrite term0. *)
(*         destruct l; auto. *)
(*         destruct l; auto. *)
(*         inv H. *)
(*         inv H. *)
(*         inv H. *)
(*       * destruct es'; auto. *)
(*         destruct (evaluate f st env (rev l)) eqn:term0; destruct r. *)
(*         apply IHf in term0. *)
(*         rewrite term0. *)
(*         destruct (op_eq_dec o Opapp). *)
(*         destruct (do_opapp (rev l0)). *)
(*         destruct p. *)
(*         apply IHf. auto. *)
(*         inv H. *)
(*         auto. *)
(*         inv H. *)
(*         destruct (evaluate f st env [EApp o l]) eqn:term0; destruct r. *)
(*         apply IHf in term0. *)
(*         rewrite term0. *)
(*         destruct (evaluate f s env (e::es')) eqn:term1; destruct r. *)
(*         apply IHf in term1. *)
(*         rewrite term1. *)
(*         auto. *)
(*         destruct l0; auto. *)
(*         destruct l0; auto. *)
(*         inv H. *)
(*         inv H. *)
(*       * destruct es'. *)
(*         destruct (evaluate f st env [e]) eqn:term0; destruct r. *)
(*         apply IHf in term0. *)
(*         rewrite term0. *)
(*         destruct l0; auto. *)
(*         induction l. *)
(*         inv H. *)
(*         destruct a. *)
(*         destruct (NoDuplicates_dec string_dec (pat_bindings p)); *)
(*           destruct (pmatch (sec env) (refs s) p v []); auto. *)
(*         inv H. *)
(*         destruct (evaluate f st env [EMat e l]) eqn:term0; destruct r. *)
(*         apply IHf in term0. *)
(*         rewrite term0. *)
(*         destruct (evaluate f s env (e0::es')) eqn:term1; destruct r. *)
(*         apply IHf in term1. *)
(*         rewrite term1. *)
(*         auto. *)
(*         destruct l0; auto. *)
(*         destruct l0; auto. *)
(*         inv H. *)
(*         inv H. *)
(*       * destruct es'; auto. *)
(*         destruct (evaluate f st env [ELannot e l]) eqn:term0; destruct r. *)
(*         apply IHf in term0. *)
(*         rewrite term0. *)
(*         destruct (evaluate f s env (e0 :: es')) eqn:term1; destruct r. *)
(*         apply IHf in term1. *)
(*         rewrite term1. *)
(*         auto. *)
(*         destruct l0; auto. *)
(*         destruct l0; auto. *)
(*         inv H. *)
(*         inv H. *)
(* Qed. *)
(* (* COMBINE THE PREVIOUS LEMMA AND THIS LEMMA *) *)
(* Lemma inc_fuel_same_err : forall (f : nat) (es : list exp) (st st' : state A) (env : sem_env val) (err : error_result val), *)
(*     err <> Rabort Rtimeout_error -> *)
(*     evaluate f st env es = (st', Rerr err) -> *)
(*     evaluate (S f) st env es = (st', Rerr err). *)
(* Proof. *)
(*   induction f. *)
(*   - intros es st st' env err no_timeout H. inv H. *)
(*     congruence. *)
(*   - induction es as [|e es']; *)
(*       intros st st' env err no_timeout H. *)
(*     + inv H. *)
(*     + rewrite evaluate_single_step in H. *)
(*       rewrite evaluate_single_step. *)
(*       destruct e; destruct es'. *)
(*       * destruct (do_con_check (sec env) c (Datatypes.length l)). *)
(*         destruct (evaluate f st env (rev l)) eqn:term0; destruct r. *)
(*         apply (inc_fuel_same_val f (rev l) st s env l0) in term0. *)
(*         rewrite term0. *)
(*         assumption. *)
(*         apply (IHf (rev l) st s env e) in term0. *)
(*         rewrite term0. *)
(*         assumption. *)
(*         destruct e; try congruence. assumption. *)
(*       * destruct (evaluate f st env [ECon c l]) eqn:term0; destruct r. *)
(*         apply (inc_fuel_same_val f [ECon c l] st s env l0) in term0. *)
(*         rewrite term0. *)
(*         destruct l0; auto. *)
(*         destruct l0; auto. *)
(*         destruct (evaluate f s env (e::es')) eqn:term1; destruct r. *)
(*         inv H. *)
(*         inv H. *)
(*         apply (IHf (e::es') s st' env err no_timeout) in term1. *)
(*         rewrite term1. reflexivity. *)
(*         inv H. *)
(*         apply (IHf [ECon c l] st st' env err no_timeout) in term0. *)
(*         rewrite term0. reflexivity. *)
(*       * assumption. *)
(*       * destruct (evaluate f st env [EVar i]) eqn:term0; destruct r. *)
(*         apply (inc_fuel_same_val f [EVar i] st s env l) in term0. *)
(*         rewrite term0. *)
(*         destruct l; auto. *)
(*         destruct l; auto. *)
(*         destruct (evaluate f s env (e :: es')) eqn:term1; destruct r; inv H. *)
(*         apply (IHf (e::es') s st' env err no_timeout) in term1. *)
(*         rewrite term1. reflexivity. *)
(*         inv H. *)
(*         apply (IHf [EVar i] st st' env err no_timeout) in term0. *)
(*         rewrite term0. reflexivity. *)
(*       * assumption. *)
(*       * destruct (evaluate f st env [EFun v e]) eqn:term0; destruct r. *)
(*         apply (inc_fuel_same_val f [EFun v e] st s env l) in term0. *)
(*         rewrite term0. *)
(*         destruct l; auto. *)
(*         destruct l; auto. *)
(*         destruct (evaluate f s env (e0::es')) eqn:term1; destruct r; inv H. *)
(*         apply (IHf (e0::es') s st' env err no_timeout) in term1. *)
(*         rewrite term1. reflexivity. *)
(*         inv H. *)
(*         apply (IHf [EFun v e] st st' env err no_timeout) in term0. *)
(*         rewrite term0. reflexivity. *)
(*       * destruct (evaluate f st env (rev l)) eqn:term0; destruct r. *)
(*         apply (inc_fuel_same_val f (rev l) st s env l0) in term0. *)
(*         rewrite term0. *)
(*         destruct (op_eq_dec o Opapp). *)
(*         destruct (do_opapp (rev l0)). *)
(*         destruct p. *)
(*         apply (IHf [e0] s st' s0 err no_timeout) in H. *)
(*         assumption. *)
(*         assumption. *)
(*         assumption. *)
(*         inv H. *)
(*         apply (IHf (rev l) st st' env err no_timeout) in term0. *)
(*         rewrite term0. reflexivity. *)
(*       * destruct (evaluate f st env [EApp o l]) eqn:term0; destruct r. *)
(*         apply (inc_fuel_same_val f [EApp o l] st s env l0) in term0. *)
(*         rewrite term0. *)
(*         destruct l0; auto. *)
(*         destruct l0; auto. *)
(*         destruct (evaluate f s env (e::es')) eqn:term1; destruct r; inv H. *)
(*         apply (IHf (e::es') s st' env err no_timeout) in term1. *)
(*         rewrite term1. reflexivity. *)
(*         inv H. *)
(*         apply (IHf [EApp o l] st st' env err no_timeout) in term0. *)
(*         rewrite term0. reflexivity. *)
(*       * destruct (evaluate f st env [e]) eqn:term0; destruct r. *)
(*         apply (inc_fuel_same_val f [e] st s env l0) in term0. *)
(*         rewrite term0. *)
(*         destruct l0; auto. *)
(*         induction l. *)
(*         assumption. *)
(*         destruct a. *)
(*         destruct (NoDuplicates_dec string_dec (pat_bindings p)). *)
(*         destruct (pmatch (sec env) (refs s) p v []). *)
(*         apply IHl. *)
(*         apply H. *)
(*         assumption. *)
(*         apply IHf. *)
(*         assumption. *)
(*         assumption. *)
(*         assumption. *)
(*         inv H. *)
(*         apply (IHf [e] st st' env err no_timeout) in term0. *)
(*         rewrite term0. reflexivity. *)
(*       * destruct (evaluate f st env [EMat e l]) eqn:term0; destruct r. *)
(*         apply (inc_fuel_same_val f [EMat e l] st s env l0) in term0. *)
(*         rewrite term0. *)
(*         destruct l0; auto. *)
(*         destruct l0; auto. *)
(*         destruct (evaluate f s env (e0::es')) eqn:term1; destruct r; inv H. *)
(*         apply (IHf (e0::es') s st' env err no_timeout) in term1. *)
(*         rewrite term1. reflexivity. *)
(*         inv H. *)
(*         apply (IHf [EMat e l] st st' env err no_timeout) in term0. *)
(*         rewrite term0. reflexivity. *)
(*       * apply IHf; assumption. *)
(*       * destruct (evaluate f st env [ELannot e l]) eqn:term0; destruct r. *)
(*         apply (inc_fuel_same_val f [ELannot e l] st s env l0) in term0. *)
(*         rewrite term0. *)
(*         destruct l0; auto. *)
(*         destruct l0; auto. *)
(*         destruct (evaluate f s env (e0::es')) eqn:term1; destruct r; inv H. *)
(*         apply (IHf (e0::es') s st' env err no_timeout) in term1. *)
(*         rewrite term1. reflexivity. *)
(*         inv H. *)
(*         apply (IHf [ELannot e l] st st' env err no_timeout) in term0. *)
(*         rewrite term0. reflexivity. *)
(* Qed. *)

Lemma inc_fuel_same_res : forall (f : nat) (es : list exp) (st st' : state A)
                            (env : sem_env val) (res : result (list val) val),
    res <> Rerr (Rabort Rtimeout_error) ->
    evaluate f st env es = (st', res) ->
    evaluate (S f) st env es = (st', res).
Proof.
  (* destruct res; intros H. *)
  (* - apply inc_fuel_same_val. *)
  (* - apply inc_fuel_same_err. *)
  (*   destruct e; congruence. *)
  induction f.
  - intros es st st' env res NoTO H.
    inv H; congruence.
  - induction es as [|e es'];
      intros st st' env res NoTO H.
    + assumption.
    + rewrite evaluate_single_step in H.
      rewrite evaluate_single_step.
      destruct e; destruct es'.
      * destruct (do_con_check (sec env) c (Datatypes.length l)); auto.
        destruct (evaluate f st env (rev l)) eqn:term0.
        apply IHf in term0.
        rewrite term0. destruct r; auto.
        destruct r. congruence. destruct e; congruence.
      * destruct (evaluate f st env [ECon c l]) eqn:term0.
        apply IHf in term0. rewrite term0.
        destruct r.
        destruct (evaluate f s env (e::es')) eqn:term1.
        apply IHf in term1. rewrite term1.
        destruct r; congruence.
        destruct r; congruence.
        inv H. reflexivity.
        destruct r; congruence.
      * destruct (nsLookup ident_string_dec i (sev env)); auto.
      * destruct (evaluate f st env [EVar i]) eqn:term0.
        apply IHf in term0. rewrite term0.
        destruct r; auto.
        destruct (evaluate f s env (e::es')) eqn:term1.
        apply IHf in term1. rewrite term1.
        destruct r; congruence.
        destruct r; congruence.
        destruct r; congruence.
      * assumption.
      * destruct (evaluate f st env [EFun v e]) eqn:term0.
        apply IHf in term0. rewrite term0.
        destruct r; auto.
        destruct (evaluate f s env (e0::es')) eqn:term1.
        apply IHf in term1. rewrite term1.
        destruct r; congruence.
        destruct r; congruence.
        destruct r; congruence.
      * destruct (evaluate f st env (rev l)) eqn:term0.
        apply IHf in term0. rewrite term0.
        destruct r; auto.
        destruct (op_eq_dec o Opapp); auto.
        destruct (do_opapp (rev l0)).
        destruct p. apply IHf; assumption.
        assumption.
        destruct r; congruence.
      * destruct (evaluate f st env [EApp o l]) eqn:term0.
        apply IHf in term0. rewrite term0.
        destruct r; auto.
        destruct (evaluate f s env (e::es')) eqn:term1.
        apply IHf in term1. rewrite term1.
        destruct r; congruence.
        destruct r; congruence.
        destruct r; congruence.
      * destruct (evaluate f st env [e]) eqn:term0.
        apply IHf in term0. rewrite term0.
        destruct r; auto.
        destruct l0; auto.
        induction l; auto.
        destruct a.
        destruct (NoDuplicates_dec string_dec (pat_bindings p)); auto.
        destruct (pmatch (sec env) (refs s) p v []).
        apply IHl.
        assumption.
        assumption.
        apply IHf; assumption.
        destruct r; congruence.
      * destruct (evaluate f st env [EMat e l]) eqn:term0.
        apply IHf in term0. rewrite term0.
        destruct r; auto.
        destruct (evaluate f s env (e0::es')) eqn:term1.
        apply IHf in term1. rewrite term1.
        destruct r; congruence.
        destruct r; congruence.
        destruct r; congruence.
      * apply IHf; assumption.
      * destruct (evaluate f st env [ELannot e l]) eqn:term0.
        apply IHf in term0. rewrite term0.
        destruct r; auto.
        destruct (evaluate f s env (e0::es')) eqn:term1.
        apply IHf in term1. rewrite term1.
        destruct r; congruence.
        destruct r; congruence.
        destruct r; congruence.
Qed.

Lemma more_fuel_same_value : forall (f f' : nat) (st st' : state A) (env : sem_env val) (v : list val) (es : list exp),
    f <= f' ->
    evaluate f st env es = (st', Rval v) ->
    evaluate f' st env es = (st', Rval v).
Proof.
  intros f f'. generalize dependent f. induction f';
  intros f st st' env v es H1 H2.
  inv H1. auto.
  inv H1; auto.
  apply (IHf' f st st' env v es) in H0; auto.
  apply inc_fuel_same_res; auto.
  congruence.
Qed.

Lemma more_fuel_same_result : forall (f f' : nat) (st st' : state A) (env : sem_env val) (res : result (list val) val) (es : list exp),
    f <= f' ->
    res <> Rerr (Rabort Rtimeout_error) ->
    evaluate f st env es = (st', res) ->
    evaluate f' st env es = (st', res).
Proof.
  intros f f'. generalize dependent f.
  induction f';
    intros f st st' env res es H H1 contra;
    inv H; auto.
    apply inc_fuel_same_res; auto.
    apply IHf' with f; auto.
Qed.


Lemma cakeml_deterministic_val :
  forall (es : list exp) (f f' : nat) (st st' st'' : state A) (env : sem_env val) (vs vs' : list val),
    evaluate f st env es = (st', Rval vs)
    -> evaluate f' st env es = (st'', Rval vs')
    -> st' = st'' /\ vs = vs'.
Proof.
  intros es f f' st st' st'' env vs vs' H0 H1.
  destruct (PeanoNat.Nat.le_decidable f f').
  - apply (more_fuel_same_value f f' st st' env vs es H) in H0.
    rewrite H0 in H1. inv H1; split; reflexivity.
  - rewrite PeanoNat.Nat.nle_gt in H;
      apply PeanoNat.Nat.lt_le_incl in H.
    apply (more_fuel_same_value f' f st st'' env vs' es H) in H1.
    rewrite H1 in H0. inv H0; split; reflexivity.
Qed.

Lemma cakeml_deterministic_no_timeout_error :
  forall (es : list exp) (f f' : nat) (st st' st'' : state A) (env : sem_env val) (res res' : result (list val) val),
    evaluate f st env es = (st', res)
    -> evaluate f' st env es = (st'', res')
    -> res <> Rerr (Rabort Rtimeout_error)
    -> res' <> Rerr (Rabort Rtimeout_error) (* I feel like this one isn't necessary *)
    -> st' = st'' /\ res = res'.
Proof.
  intros es f f' st st' st'' env res res' H0 H1 H2 H3.
  destruct (PeanoNat.Nat.le_decidable f f').
  - apply (more_fuel_same_result f f' st st' env res es H H2) in H0.
    rewrite H0 in H1. inv H1; split; reflexivity.
  - rewrite PeanoNat.Nat.nle_gt in H;
      apply PeanoNat.Nat.lt_le_incl in H.
    apply (more_fuel_same_result f' f st st'' env res' es H H3) in H1.
    rewrite H0 in H1. inv H1; split; reflexivity.
Qed.

Lemma NoTO_val : forall (v : list val), @Rval (list val) val v <> Rerr (Rabort Rtimeout_error).
Proof. congruence. Qed.

(* Lemma replace_subexp_fuel : *)
(*   forall (e : exp) (es : list exp) (f' : nat) (st st' : state A) (env : sem_env val) (res : result (list val) val), *)
(*       is_subexp e es *)
(*       -> res <> Rerr (Rabort Rtimeout_error) *)
(*       -> evaluate f' st env es = (st', res) *)
(*       -> exists st'' res', evaluate f' st env [e] = (st'', res') *)
(*       /\ res' <> Rerr (Rabort Rtimeout_error). *)
(* Proof. *)
(*   intros e es f' st st' env res Hsubexp. *)
(*   generalize dependent res. *)
(*   generalize dependent env. *)
(*   generalize dependent st'. *)
(*   generalize dependent st. *)
(*   generalize dependent f'. *)
(*   induction Hsubexp. *)
(*   * intros f' st st' env res Hres H0. *)
(*     rewrite H0. exists st'. exists res. split; congruence. *)
(*   * intros f' st st' env res Hres H0. *)
(*     destruct H. *)
(*     apply inc_fuel_same_res in H0; try (congruence). *)
(*     rewrite evaluate_single_step in H0. *)

(*     inv H. *)

Theorem plus_vs_cake_plus : forall (m n t f : nat) (m_exp n_exp : exp) (m_val n_val m_n_val : val),
    evaluate f my_st my_env [m_exp] = (my_st, Rval [m_val]) ->
    evaluate f my_st my_env [n_exp] = (my_st, Rval [n_val]) ->
    nat_rel_cake_nat t m m_val ->
    nat_rel_cake_nat t n n_val ->
    evaluate f my_st my_env [(EApp (Opapp) ((EApp (Opapp) ((EVar (Short ("plus"%string)))::m_exp::nil))::n_exp::nil))] =
    (my_st, Rval [m_n_val]) ->
    nat_rel_cake_nat t (m+n) m_n_val.
Proof.
  intros m n t f m_exp n_exp m_val n_val m_n_val Hmf Hnf Hrelm Hreln Hmnf.
  destruct t. (* Do not like this but may be easier *)
  inv Hreln.
  - apply inc_fuel_same_res in Hmnf; try (congruence).
    apply inc_fuel_same_res in Hmnf; try (congruence).
    simpl in Hmnf.
    rewrite Hnf in Hmnf. simpl in Hmnf.
    destruct n_exp.
    break_let.
    break_let.
    apply inc_fuel_same_res in Heqp0; try (congruence).
    apply inc_fuel_same_res in Heqp0; try (congruence).
    simpl in Heqp0.
    destruct m_exp.
    rewrite Hmf in Heqp0.
    break_let.
    break_let.
    apply inc_fuel_same_res in Heqp2; try (congruence).
    simpl in Heqp2.
    inv Heqp2.
