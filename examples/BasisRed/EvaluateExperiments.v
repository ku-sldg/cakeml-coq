Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Require Import StructTact.StructTactics.
Require Import Omega.
Require Import Coq.Logic.Eqdep_dec.
Require Import Equations.Equations.

Require Import CakeSem.Utils.
Require Import FFI.
Require Import CakeSem.Namespace.
Require Import CakeSem.CakeAST.
Require Import CakeSem.SemanticsAux.
Require Import CakeSem.Evaluate.

Require Import BasisPlus.
Require Import BasisEvaluated.

(* Definition init_env : sem_env val := empty_sem_env. *)
(* Definition init_store := empty_store val. *)
(* Parameter init_ffi_st : ffi_state nat. *)
(* Definition init_state := Build_state 0 init_store init_ffi_st 0 0. *)

Theorem evaluate_decs_Dmod : forall (fuel : nat) (mn : modN) (st st' : state nat) (env env' : sem_env val) (ds : list dec),
    evaluate_decs fuel st env ds = (st', Rval env') ->
    evaluate_decs fuel st env [Dmod mn ds] = (st', Rval {| sev := nsLift mn (sev env'); sec := nsLift mn (sec env') |}).
Proof.
  intros.
  simp evaluate_decs.
  rewrite H.
  reflexivity.
Qed.

Theorem evaluate_decs_Dlocal : forall (fuel : nat) (st st' st'' : state nat) (env env' env'' : sem_env val) (ds1 ds2 : list dec),
    evaluate_decs fuel st env ds1 = (st', Rval env') ->
    evaluate_decs fuel st' (extend_dec_env env' env) ds2 = (st'', Rval env'') ->
    evaluate_decs fuel st env [Dlocal ds1 ds2] = (st'', Rval env'').
Proof.
  intros.
  simp evaluate_decs.
  rewrite H.
  simpl.
  rewrite H0.
  reflexivity.
Qed.

Theorem extend_empty_r : forall V (env : sem_env V),
    extend_dec_env env {| sev := nsEmpty; sec := nsEmpty |} = env.
Proof.
  intros.
  destruct env.
  unfold extend_dec_env.
  unfold nsAppend.
  simpl.
  unfold nsEmpty.
  repeat rewrite app_nil_r.
  reflexivity.
Qed.

Theorem extend_empty_l : forall V (env : sem_env V),
    extend_dec_env {| sev := nsEmpty; sec := nsEmpty |} env = env.
Proof.
  intros.
  destruct env.
  unfold extend_dec_env.
  unfold nsAppend.
  reflexivity.
Qed.



Theorem evaluate_0_26_correct :
  evaluate_decs 100 init_state init_env prog_0_26 =
  (st_0_26, Rval env_0_26).
Proof.
  reflexivity.
Qed.

Theorem evaluate_0_27_correct :
  evaluate_decs 100 init_state init_env (prog_0_26 ++ [dec_def_27]) =
  (st_0_26, Rval env_27).
Proof.
  reflexivity.
Qed.

Theorem evaluate_0_29_correct :
  evaluate_decs 100 init_state init_env (prog_0_26 ++ [dec_def_27; dec_def_28; dec_def_29]) =
  (st_0_26, Rval env_28_29).
Proof.
  reflexivity.
Qed.

(* Theorem evaluate_0_30_correct : *)
(*   evaluate_decs 100 init_state init_env (prog_0_26 ++ [dec_def_27; dec_def_28; dec_def_29; dec_def_30]) = *)
(*   (st_0_26, Rval env_30). *)
(* Proof. *)
(*   reflexivity. *)
(* Qed. *)

Ltac evaluate_decs_one :=
  match goal with
  | [|- evaluate_decs _ _ _ [?def] = (_, Rval _)] =>
    unfold def;
    match goal with
    | [|- evaluate_decs _ _ _ [Dmod _ _] = (_, Rval _)]   => erewrite evaluate_decs_Dmod
    | [|- evaluate_decs _ _ _ [Dlocal _ _] = (_, Rval _)] => erewrite evaluate_decs_Dlocal
    | [|- evaluate_decs _ _ _ [_] = (_, Rval _)] => simp evaluate_decs
    end; try reflexivity
  end.

Ltac evaluate_decs_noapp :=
  match goal with
  | [|- evaluate_decs _ _ _ [] = (_, Rval _)] => simp evaluate_decs; reflexivity
  | [|- evaluate_decs _ _ _ [_] = (_, Rval _)] => evaluate_decs_one
  | [|- evaluate_decs _ _ _ (?def::_) = (_, Rval _)] =>
    eapply evaluate_decs_cons'; [evaluate_decs_one | unfold extend_dec_env; simpl]
  end.

Transparent evaluate_decs.
Eval compute in evaluate_decs 100 init_state init_env prog.

Theorem evaluate_30 : exists env st,
    evaluate_decs 100 st_0_26 env_28_29 [dec_def_30; dec_def_31] =
    (st, Rval env).
Proof.
  econstructor; econstructor.

  Transparent evaluate_decs.


  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  (* HERE *)
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  evaluate_decs_noapp.
  eapply evaluate_decs_cons'.

  + unfold dec_def_30;
      erewrite evaluate_decs_Dmod; [reflexivity | simpl].

  eapply evaluate_decs_cons'.
  unfold dec_def_30_0;
    simp evaluate_decs; simpl;
      reflexivity.
  rewrite extend_empty_l.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_1;
    simp evaluate_decs; simpl;
      reflexivity.
  unfold extend_dec_env.
      simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_2.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_3.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_4.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_5.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_6.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_7.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_8.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_9.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  unfold dec_def_30_10.
  erewrite evaluate_decs_Dlocal.
  reflexivity.

  unfold dec_def_30_10_0.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_10_1.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_10_2.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  unfold dec_def_30_10_3.
  erewrite evaluate_decs_Dlocal.
  reflexivity.

  unfold dec_def_30_10_3_0.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_10_3_1.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  unfold dec_def_30_10_3_2.
  erewrite evaluate_decs_Dlocal.
  reflexivity.

  unfold dec_def_30_10_3_2_0.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_10_3_2_1.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  unfold dec_def_30_10_3_2_2.
  erewrite evaluate_decs_Dlocal.
  reflexivity.

  unfold dec_def_30_10_3_2_2_0.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_10_3_2_2_1.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  unfold dec_def_30_10_3_2_2_2.
  erewrite evaluate_decs_Dlocal.
  reflexivity.

  unfold dec_def_30_10_3_2_2_2_0.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_10_3_2_2_2_1.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  unfold dec_def_30_10_3_2_2_2_2.
  erewrite evaluate_decs_Dlocal.
  reflexivity.

  unfold dec_def_30_10_3_2_2_2_2_0.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_10_3_2_2_2_2_1.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_10_3_2_2_2_2_2.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_10_3_2_2_2_2_3.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_10_3_2_2_2_2_4.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  unfold dec_def_30_10_3_2_2_2_2_5.
  erewrite evaluate_decs_Dlocal.
  reflexivity.

  unfold dec_def_30_10_3_2_2_2_2_5_0.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_10_3_2_2_2_2_5_1.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_10_3_2_2_2_2_5_2.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_10_3_2_2_2_2_5_3.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_10_3_2_2_2_2_5_4.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  eapply evaluate_decs_cons'.
  unfold dec_def_30_10_3_2_2_2_2_5_5.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  unfold dec_def_30_10_3_2_2_2_2_5_6.
  erewrite evaluate_decs_Dlocal.
  reflexivity.

  unfold dec_def_30_10_3_2_2_2_2_5_6_0.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env.
  simpl.

  unfold dec_def_30_10_3_2_2_2_2_5_6_1.
  simp evaluate_decs; simpl.
  reflexivity.
  unfold extend_dec_env at 1.
  simpl.

Qed.

(* Theorem evaluate_0_26 : exists env st, *)
(*     evaluate_decs 100 init_state init_env prog_0_26 = *)
(*     (st, Rval env). *)
(* Proof. *)
(*   econstructor. econstructor. *)
(*   unfold prog_0_26. *)
(*   unfold init_state. *)
(*   unfold init_env. *)
(*   unfold empty_sem_env. *)
(*   unfold nsEmpty. *)
(*   simpl. *)
(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_0. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_2. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_3. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_4. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_5. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_6. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_7. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_8. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_9. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_10. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_11. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_12. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_13. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_14. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_15. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_16. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_17. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_18. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_19. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_20. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_21. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_22. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_23. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_24. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_25. (* Runtime Module (5 subdefs) *) *)
(*   erewrite evaluate_decs_Dmod. *)
(*   reflexivity. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_25_0. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_25_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_25_2. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_25_3. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_25_4. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_25_5. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   simp evaluate_decs; simpl. *)

(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_26. (* Option module *) *)
(*   erewrite evaluate_decs_Dmod. *)
(*   reflexivity. *)
(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_26_0. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_26_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_26_2. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_26_3. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_26_4. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_26_5. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_26_6. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_26_7. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_26_8. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_26_9. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_26_10. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold state_update_next_type_stamp. *)
(*   simpl. *)

(*   unfold dec_def_26_11. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)

(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(* Qed. *)

(* Theorem evaluate_27 : exists env st, *)
(*     evaluate_decs 100 st_0_26 env_0_26 [dec_def_27] = *)
(*     (st, Rval env). *)
(*   econstructor. econstructor. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27. *)
(*   eapply evaluate_decs_Dmod. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_0. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   simpl. *)

(*   unfold dec_def_27_2. (* First Dlocal *) *)
(*   erewrite evaluate_decs_Dlocal. *)
(*   reflexivity. *)

(*   unfold dec_def_27_2_0. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   unfold build_rec_env. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   unfold dec_def_27_2_2. *)
(*   erewrite evaluate_decs_Dlocal. *)
(*   reflexivity. *)

(*   unfold dec_def_27_2_2_0. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; simpl. *)
(*   unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_2. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_3. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_4. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_5. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_6. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_7. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_8. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_9. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_10. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; simpl. *)
(*   unfold nsBind. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_11. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_12. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_13. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_14. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env. *)
(*   simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15. *)
(*   erewrite evaluate_decs_Dlocal. *)
(*   reflexivity. *)

(*   unfold dec_def_27_2_2_15_0. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_2. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_3. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_4. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_5. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   unfold dec_def_27_2_2_15_6. *)
(*   erewrite evaluate_decs_Dlocal. *)
(*   reflexivity. *)
(*   unfold dec_def_27_2_2_15_6_0. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_2. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   unfold dec_def_27_2_2_15_6_3. *)
(*   erewrite evaluate_decs_Dlocal. *)
(*   reflexivity. *)
(*   unfold dec_def_27_2_2_15_6_3_0. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_2. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_3. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_4. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_5. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_6. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_7. *)
(*   erewrite evaluate_decs_Dlocal. *)
(*   reflexivity. *)

(*   unfold dec_def_27_2_2_15_6_3_7_0. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_7_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_7_2. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_7_3. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_7_4. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_7_5. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_7_6. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_7_7. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_7_8. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_7_9. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_7_10. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_7_11. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_7_12. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_7_13. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_7_14. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_7_15. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_7_16. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   unfold dec_def_27_2_2_15_6_3_7_17. *)

(*   erewrite evaluate_decs_Dlocal. *)
(*   reflexivity. *)
(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_27_2_2_15_6_3_7_17_0. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   unfold dec_def_27_2_2_15_6_3_7_17_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   unfold dec_def_27_2_2_15_6_3_7_17_2. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env at 1. *)
(*   simpl. *)

(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)

(*   unfold extend_dec_env at 1. *)
(*   simpl. *)

(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(* Qed. *)

(* Theorem evaluate_28_29 : exists env st, *)
(*     evaluate_decs 100 st_0_26 env_27 [dec_def_28; dec_def_29] = *)
(*     (st, Rval env). *)
(*   econstructor. econstructor. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_28. (* AList Module *) *)
(*   erewrite evaluate_decs_Dmod. *)
(*   reflexivity. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_28_0. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_28_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_28_2. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_28_3. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_28_4. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_28_5. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)

(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_29. (* Vector module *) *)
(*   erewrite evaluate_decs_Dmod. *)
(*   reflexivity. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_29_0. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_29_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_29_2. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_29_3. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_29_4. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   unfold dec_def_29_5. *)
(*   erewrite evaluate_decs_Dlocal. *)
(*   reflexivity. *)

(*   unfold dec_def_29_5_0. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_29_5_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_29_5_2. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_29_5_3. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_29_5_4. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_29_5_5. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   unfold dec_def_29_5_6. *)
(*   erewrite evaluate_decs_Dlocal. *)
(*   reflexivity. *)
(*   unfold dec_def_29_5_6_0. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_29_5_6_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   unfold dec_def_29_5_6_2. *)
(*   erewrite evaluate_decs_Dlocal. *)
(*   reflexivity. *)
(*   unfold dec_def_29_5_6_2_0. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_29_5_6_2_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   unfold dec_def_29_5_6_2_2. *)
(*   erewrite evaluate_decs_Dlocal. *)
(*   reflexivity. *)
(*   unfold dec_def_29_5_6_2_2_0. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_29_5_6_2_2_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   unfold dec_def_29_5_6_2_2_2. *)
(*   erewrite evaluate_decs_Dlocal. *)
(*   reflexivity. *)
(*   unfold dec_def_29_5_6_2_2_2_0. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_29_5_6_2_2_2_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   unfold dec_def_29_5_6_2_2_2_2. *)
(*   erewrite evaluate_decs_Dlocal. *)
(*   reflexivity. *)

(*   unfold dec_def_29_5_6_2_2_2_2_0. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_29_5_6_2_2_2_2_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   unfold dec_def_29_5_6_2_2_2_2_2. *)
(*   erewrite evaluate_decs_Dlocal. *)
(*   reflexivity. *)

(*   unfold dec_def_29_5_6_2_2_2_2_2_0. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_29_5_6_2_2_2_2_2_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   unfold dec_def_29_5_6_2_2_2_2_2_2. *)
(*   erewrite evaluate_decs_Dlocal. *)
(*   reflexivity. *)

(*   unfold dec_def_29_5_6_2_2_2_2_2_2_0. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_29_5_6_2_2_2_2_2_2_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   unfold dec_def_29_5_6_2_2_2_2_2_2_2. *)
(*   erewrite evaluate_decs_Dlocal. *)
(*   reflexivity. *)

(*   unfold dec_def_29_5_6_2_2_2_2_2_2_2_0. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   eapply evaluate_decs_cons'. *)
(*   unfold dec_def_29_5_6_2_2_2_2_2_2_2_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   unfold dec_def_29_5_6_2_2_2_2_2_2_2_2. *)
(*   erewrite evaluate_decs_Dlocal. *)
(*   reflexivity. *)

(*   unfold dec_def_29_5_6_2_2_2_2_2_2_2_2_0. *)
(*   simp evaluate_decs; simpl. *)
(*   unfold build_rec_env; unfold nsBind; simpl. *)
(*   reflexivity. *)
(*   unfold extend_dec_env; simpl. *)

(*   unfold dec_def_29_5_6_2_2_2_2_2_2_2_2_1. *)
(*   simp evaluate_decs; simpl. *)
(*   reflexivity. *)
(*   (* ENDS HERE *) *)
(* Qed. *)
