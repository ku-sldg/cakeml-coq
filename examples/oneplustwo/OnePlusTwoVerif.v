(* From TLC Require Import LibLogic LibReflect. *)
(* From TLC Require Import LibListZ. *)

Require Import List.
Import ListNotations.
Require Import String.
Require Import ZArith.

Require Import CakeSem.Namespace.
Require Import CakeSem.CakeAST.
Require Import CakeSem.SemanticsAux.
Require Import CakeSem.RelationalBigStep.

Require Import Infra.CakeBasisLib.

(* Require Import BSRelAutomation. *)

Axiom alreadyTypeChecked : RelationalBigStep.doTypeChecks = false.
Hint Resolve alreadyTypeChecked.

Definition plus_dec := dec_def_31.

Definition opt_program x y := (Dlet [(0%nat)] (Pvar ("x"%string)) (ELannot (EApp (Opapp) ((EApp (Opapp) ((EVar (Short ("+"%string)))::(ELannot (ELit (IntLit x)) [(0%nat)])::nil))::(ELannot (ELit (IntLit y)) [(0%nat)])::nil)) [(0%nat)])).

Lemma plus_env : forall (A:Type) (st : state A) (env env1 : sem_env val),
    env = Build_sem_env nsEmpty nsEmpty ->
    env1 = extend_dec_env env (update_sev env [(Short "+", Closure env "v1" (EFun "v2" (EApp (Opn Plus) [(EVar (Short "v1")); (EVar (Short "v2"))])))]) ->
    decR st env plus_dec (st, Rval env1).
Proof.
  intros.
  econstructor.
  (* apply decR_Dlet with ([("+", Closure env "v1" (EFun "v2" (EApp (Opn Plus) [(EVar (Short "v1")); (EVar (Short "v2"))])))]) *)
  (*                      (Closure env "v1" (EFun "v2" (EApp (Opn Plus) [(EVar (Short "v1")); (EVar (Short "v2"))]))). *)
  unfold TypeCheck; rewrite alreadyTypeChecked; trivial.
  econstructor.
  econstructor.
  rewrite H in *. simpl in *. unfold update_sev in H0. simpl in H0. assumption.
Qed.

(* Thoughts: What is the proper way to update the environment from an ease of use perspective?
 * What lemma's are necessary for unbridled use? *)
Theorem one_plus_two_is_three : forall (A:Type) (x y : Z) (st: state A) (env env0 env1: sem_env val),
    let plus_clos := Closure env "v1" (EFun "v2" (EApp (Opn Plus) [(EVar (Short "v1"));
                                                                   (EVar (Short "v2"))]))
    in
    env = empty_sem_env ->
    env0 = extend_dec_env (Build_sem_env
                             [(Short "+", plus_clos)]
                             nsEmpty)
                          env ->
    env1 = extend_dec_env
             (extend_dec_env empty_sem_env (Build_sem_env [(Short "x", Litv (IntLit (x+y)))] nsEmpty))
             env0 ->
    decListR st env [plus_dec; opt_program x y] (st, Rval env1).
Proof.
  intros.
  rewrite H1.
  econstructor.
  - apply plus_env.
    rewrite H. reflexivity.
    rewrite H0; unfold plus_clos; rewrite H; simpl; unfold extend_dec_env; reflexivity.
  - econstructor.
    + econstructor.
      * unfold TypeCheck; rewrite alreadyTypeChecked; trivial.
      *  econstructor.
         econstructor.
         econstructor.
         econstructor.
         econstructor.
         econstructor.
         econstructor.
         econstructor.
         econstructor.
         econstructor.
         econstructor.
         econstructor.
         econstructor.
         econstructor.
         rewrite H0, H. simpl. apply LibLogic.If_l. reflexivity.
         econstructor.
         econstructor.
         econstructor.
         econstructor.
         econstructor.
         econstructor.
         discriminate.
         econstructor.
         econstructor.
         econstructor.
         econstructor.
         simpl. rewrite LibLogic.If_l.
         reflexivity. reflexivity.
         econstructor.
         simpl. rewrite LibLogic.If_r.
         simpl. rewrite LibLogic.If_l.
         reflexivity. reflexivity.
         discriminate.
         econstructor.
         intro H2.
         inversion H2.
         inversion H3.
         inversion H3.
         econstructor.
      * econstructor.
      * reflexivity.
    + destruct st; apply decR_Dnil.
Qed.
