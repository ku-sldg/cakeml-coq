Require Import Lists.List.
Import ListNotations.

Require Import CakeSem.Namespace.
Require Import CakeSem.CakeAST.
Require Import CakeSem.SemanticsAux.
Require Import CakeSem.Evaluate.
Require Import StructTact.StructTactics.

From Equations Require Import Equations.

Definition ST := nat.

Theorem eval_or_match_true_ignore : forall (st : state nat) (env : sem_env val) (es : list exp) (f : nat)
                                      (u1 u2 u3 u4 : val),
    eval_or_match true es f st env u1 u2 = eval_or_match true es f st env u3 u4.
Proof.
  intros st env es. revert st env.
  induction es. intros.
  simp eval_or_match. congruence.
  destruct es; intros; simp eval_or_match; eauto.
  destruct a; simp eval_or_match; eauto.
  + destruct (do_con_check (sec env) c (Datatypes.length l)); eauto.
  + destruct (nsLookup ident_string_beq i (sev env)); eauto.
  + destruct f; simp eval_or_match; simpl in *; eauto.
    destruct (eval_or_match true (rev l) f st env uu uu); simpl in *; eauto.
    break_match; simpl in *; eauto.
    destruct (op_beq o Opapp); simpl in *; eauto.
  + destruct l; simp eval_or_match; simpl in *; eauto.
Qed.

Theorem eval_or_match_cons : forall (st : state nat) (env : sem_env val) (e : exp) (es : list exp) (f : nat),
   eval_or_match true (e::es) f st env uu uu =
     match eval_or_match true [e] f st env uu uu with
     | (st', Rval vs) =>
      match eval_or_match true es f st' env uu uu with
       | (st'', Rval vs') => (st'', Rval (vs++vs'))
       | err => err
      end
     | err => err
     end.
Proof.
  intros. revert e st.
  destruct es; intros; simp eval_or_match; eauto.
  - destruct (eval_or_match true [e] f st env uu uu).
    break_match; simpl in *; eauto.
    simp eval_or_match.
    rewrite app_nil_r.
    congruence.
  - break_let; eauto.
    break_match; eauto.
    apply eval_or_match_sing in Heqp.
    destruct Heqp. subst. simpl.
    destruct (eval_or_match true (e::es) f s env uu uu).
    simpl in *. break_match; eauto.
Qed.

Theorem evaluate_decs_cons : forall (fuel : nat) (st : state nat) (env : sem_env val) (d : dec) (ds : list dec),
   evaluate_decs fuel st env (d::ds) =
     match evaluate_decs fuel st env [d] with
     | (s1, Rval env1) =>
       match evaluate_decs fuel s1 (extend_dec_env env1 env) ds with
       | (s2, r) => (s2, combine_dec_result env1 r)
       end
     | err => err
     end.
Proof.
  intros.
  destruct ds.
  break_let.
  break_match.
  break_let.
  simp evaluate_decs in Heqp0.
  inv Heqp0.
  simpl.
  unfold extend_dec_env.
  simpl.
  destruct s0. simpl.
  reflexivity.
  reflexivity.
  simp evaluate_decs.
  reflexivity.
Qed.

Theorem evaluate_decs_app : forall (fuel : nat) (st : state nat) (env : sem_env val) (ds1 ds2 : list dec),
   evaluate_decs fuel st env (ds1 ++ ds2) =
     match evaluate_decs fuel st env ds1 with
     | (s1, Rval env1) =>
       match evaluate_decs fuel s1 (extend_dec_env env1 env) ds2 with
       | (s2, r) => (s2, combine_dec_result env1 r)
       end
     | err => err
     end.
Proof.
  intros. revert fuel st env ds2.
  induction ds1.
  - intros. simpl.
    simp evaluate_decs.
    unfold combine_dec_result.
    unfold extend_dec_env.
    rewrite (sem_env_id env).
    simpl.
    break_let.
    break_match.
    + unfold nsAppend.
      unfold nsEmpty.
      rewrite app_nil_r.
      rewrite app_nil_r.
      rewrite (sem_env_id s0).
      reflexivity.
    + reflexivity.
  - intros. simpl.
    rewrite evaluate_decs_cons.
    destruct (evaluate_decs fuel st env [a]) eqn:eval1.
    rewrite evaluate_decs_cons.
    rewrite eval1.
    destruct r.
    rewrite IHds1.
    unfold extend_dec_env.
    unfold nsAppend.
    simpl.
    destruct
      (evaluate_decs fuel s {| sev := sev s0 ++ sev env; sec := sec s0 ++ sec env |} ds1) eqn:eval2.
    destruct r.
    destruct s0.
    simpl.
    unfold nsAppend.
    simpl.
    rewrite app_assoc_reverse.
    rewrite app_assoc_reverse.
    destruct (evaluate_decs fuel s1
         {|
         sev := SemanticsAux.sev s2 ++ sev ++ SemanticsAux.sev env;
         sec := SemanticsAux.sec s2 ++ sec ++ SemanticsAux.sec env |} ds2).
    unfold combine_dec_result.
    unfold extend_dec_env.
    simpl.
    unfold nsAppend.
    simpl.
    destruct r.
    simpl.
    rewrite app_assoc_reverse.
    rewrite app_assoc_reverse.
    reflexivity.
    reflexivity.
    destruct s0.
    simpl.
    reflexivity.
    reflexivity.
Qed.

Theorem evaluate_decs_app' : forall (fuel : nat) (st st' st'' : state nat) (env env' env'' : sem_env val) (ds1 ds2 : list dec),
    evaluate_decs fuel st env ds1 = (st', Rval env') ->
    evaluate_decs fuel st' (extend_dec_env env' env) ds2 = (st'', Rval env'') ->
    evaluate_decs fuel st env (ds1 ++ ds2) = (st'', Rval (extend_dec_env env'' env')).
Proof.
  intros.
  rewrite evaluate_decs_app.
  rewrite H.
  rewrite H0.
  simpl.
  reflexivity.
Qed.

Theorem evaluate_decs_cons' : forall (fuel : nat) (st st' st'' : state nat) (env env' env'' : sem_env val) (d : dec) (ds : list dec),
    evaluate_decs fuel st env [d] = (st', Rval env') ->
    evaluate_decs fuel st' (extend_dec_env env' env) ds = (st'', Rval env'') ->
    evaluate_decs fuel st env (d::ds) = (st'', Rval (extend_dec_env env'' env')).
Proof.
  intros.
  assert (d::ds = [d] ++ ds) by reflexivity.
  rewrite H1.
  rewrite evaluate_decs_app.
  rewrite H.
  rewrite H0.
  simpl.
  reflexivity.
Qed.

Lemma eval_or_match_inc_fuel_res : forall (f : nat) (sel : bool)
                                     (es : if sel then list exp else list (pat * exp)) (st st' : state ST)
                                     (env : sem_env val) (match_v err_v : val) (res : result (list val) val),
    res <> Rerr (Rabort Rtimeout_error) ->
    eval_or_match sel es f st env match_v err_v = (st', res) ->
    eval_or_match sel es (S f) st env match_v err_v = (st', res).
Proof.
  intros.
  (* 43 cases :>( *)
  funelim (eval_or_match sel es f st env match_v err_v);
  (* eliminates 8 cases *)
  simp eval_or_match in *;
  (* eliminates 10 cases *)
  try (rewrite Heq in H0, Heqcall;
       apply Hind in Heq; (try discriminate);
       rewrite Heq; simpl in *; assumption).
  - inv H0. contradiction.
  - break_match; try (assumption).
    apply H; assumption.
  - break_match; try assumption.
    break_match; try assumption.
    apply H; assumption.
    eapply H0; try assumption; try reflexivity.
  - rewrite Heq in H0, Heqcall; apply Hind in Heq; try (discriminate);
    rewrite Heq in *; simpl in *.
    assumption.
    inv H0. assumption.
  - rewrite Heq in Heqcall, H1.
    apply Hind in Heq; try discriminate.
    rewrite Heq in *; simpl in *.
    apply H; assumption.
  - rewrite Heq in Heqcall, H0; simpl in *.
    apply Hind in Heq.
    rewrite Heq in *; simpl in *.
    assumption.
    inv H0.
    assumption.
  - rewrite Heq in Heqcall, H0.
    rewrite Heq in *; simpl in *.
    assumption.
  - rewrite Heq0 in *. simpl in *.
    rewrite Heq in H0, Heqcall.
    apply Hind in Heq.
    rewrite Heq. simpl in *.
    assumption.
    rewrite H0 in Heqcall.
    inv Heqcall. assumption.
  - rewrite Heq1 in *. simpl in *. rewrite Heq0 in Heqcall, H0.
    simpl in *. apply Hind in Heq0; try discriminate.
    rewrite Heq0. simpl in *. rewrite Heq in *. simpl in *.
    assumption.
  - rewrite Heq1 in *. simpl in *.
    rewrite Heq0 in H0, Heqcall.
    apply Hind in Heq0; try discriminate.
    rewrite Heq0. simpl in *.
    rewrite Heq in *. simpl in *.
    assumption.
  - rewrite Heq in H0, Heqcall.
    apply Hind in Heq.
    rewrite Heq in *. simpl in *.
    assumption.
    rewrite H0 in Heqcall. inv Heqcall. assumption.
  - rewrite Heq1 in H1, Heqcall. apply Hind in Heq1; try discriminate.
    rewrite Heq1. simpl in *.
    rewrite Heq0 in *. simpl in *.
    rewrite Heq in *. simpl in *.
    apply H; assumption.
  - rewrite Heq1 in H0, Heqcall.
    apply Hind in Heq1; try discriminate.
    rewrite Heq1. simpl in *.
    rewrite Heq0 in *; simpl in *.
    rewrite Heq in *; simpl in *.
    assumption.
  - rewrite Heq1 in H0, Heqcall.
    apply Hind in Heq1; try discriminate.
    rewrite Heq1; simpl in *.
    rewrite Heq0 in *; simpl in *.
    rewrite Heq in *; simpl in *.
    assumption.
  - rewrite Heq1 in H0, Heqcall.
    apply Hind in Heq1; try discriminate.
    rewrite Heq1; simpl in *.
    rewrite Heq0 in *; simpl in *.
    rewrite Heq in *; simpl in *.
    assumption.
  - rewrite Heq in H1, Heqcall.
    apply Hind in Heq; try discriminate.
    rewrite Heq in *. simpl in *.
    break_match; try assumption.
    apply H; assumption.
  - rewrite Heq in H0, Heqcall.
    apply Hind in Heq; try discriminate.
    rewrite Heq; simpl in *.
    assumption.
    rewrite H0 in Heqcall. inv Heqcall. assumption.
  - rewrite Heq in H1, Heqcall.
    apply Hind in Heq; try discriminate.
    rewrite Heq; simpl in *.
    break_match; try assumption.
    break_match; try assumption.
    apply H; assumption.
  - rewrite Heq in H0, Heqcall.
    apply Hind in Heq; try discriminate.
    rewrite Heq. simpl in *.
    assumption.
    rewrite H0 in Heqcall. inv Heqcall. assumption.
  - rewrite Heq in H2, Heqcall.
    apply Hind in Heq; try discriminate.
    rewrite Heq; simpl in *.
    break_match; try assumption.
    apply H; try assumption.
    break_match; try assumption.
    apply H0; try assumption.
  - rewrite Heq in H0, Heqcall.
    apply Hind in Heq; try discriminate.
    rewrite Heq; simpl in *.
    assumption.
    rewrite H0 in Heqcall; inv Heqcall; assumption.
  - rewrite Heq in H1, Heqcall.
    apply Hind in Heq; try discriminate.
    rewrite Heq; simpl in *.
    apply H; try assumption.
  - rewrite Heq in H0, Heqcall.
    apply Hind in Heq; try discriminate.
    rewrite Heq; simpl in *.
    assumption.
    rewrite H0 in Heqcall; inv Heqcall; assumption.
  - rewrite Heq in H1, Heqcall.
    apply Hind in Heq; try discriminate.
    rewrite Heq; simpl in *.
    apply H; try assumption.
  - rewrite Heq in H0, Heqcall.
    apply Hind in Heq; try discriminate.
    rewrite Heq; simpl in *.
    assumption.
    rewrite H0 in Heqcall; inv Heqcall; assumption.
  - rewrite Heq in H0, Heqcall.
    apply Hind in Heq; try discriminate.
    rewrite Heq; simpl in *.
    assumption.
    rewrite H0 in Heqcall; inv Heqcall; assumption.
  - rewrite Heq0 in H0, Heqcall.
    apply Hind0 in Heq0; try discriminate.
    rewrite Heq0; simpl in *.
    rewrite Heq in H0, Heqcall.
    apply Hind in Heq; try discriminate.
    rewrite Heq; simpl in *.
    assumption.
    rewrite H0 in Heqcall; inv Heqcall; assumption.
  - rewrite Heq0 in H0, Heqcall.
    apply Hind0 in Heq0; try discriminate.
    rewrite Heq0; simpl in *.
    rewrite Heq in H0, Heqcall.
    apply Hind in Heq; try discriminate.
    rewrite Heq; simpl in *.
    assumption.
  - rewrite Heq0 in H0, Heqcall.
    apply Hind0 in Heq0; try discriminate.
    rewrite Heq0; simpl in *.
    rewrite Heq in H0, Heqcall.
    apply Hind in Heq; try discriminate.
    rewrite Heq; simpl in *.
    assumption.
Qed.

Lemma inc_fuel_same_val : forall (f : nat) (e : exp) (st st' : state ST)
                            (env : sem_env val) (v : val),
    evaluate [e] f st env = (st', Rval [v]) ->
    evaluate [e] (S f) st env = (st', Rval [v]).
Proof.
  unfold evaluate.
  intros.
  apply eval_or_match_inc_fuel_res; try discriminate.
  assumption.
Qed.

Lemma more_fuel_same_value : forall (f f' : nat) (st st' : state ST) (env : sem_env val) (v : list val) (es : list exp),
    f <= f' ->
    evaluate es f st env = (st', Rval v) ->
    evaluate es f' st env = (st', Rval v).
Proof.
  unfold evaluate.
  intros f f' st st' env v es H H'.
  induction H.
  - assumption.
  - apply eval_or_match_inc_fuel_res; try discriminate.
    assumption.
Qed.

Lemma more_fuel_same_result : forall (f f' : nat) (st st' : state ST) (env : sem_env val) (res : result (list val) val) (es : list exp),
    f <= f' ->
    res <> Rerr (Rabort Rtimeout_error) ->
    evaluate es f st env = (st', res) ->
    evaluate es f' st env = (st', res).
Proof.
  unfold evaluate.
  intros f f' st st' env res es H H' H''.
  induction H.
  assumption.
  apply eval_or_match_inc_fuel_res; assumption.
Qed.
