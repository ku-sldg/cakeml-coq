Require Import Lia.
Require Import Lists.List.
Import ListNotations.

Require Import CakeSem.Utils.
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

Lemma eval_or_match_ECon_exists_Conv : forall name es f st st' env v, eval_or_match true [ECon name es] f st env uu uu = (st', Rval [v]) ->
                            exists stmp vs, v = Conv stmp vs.
Proof.
  intros name es f st st' env v H.
  funelim (eval_or_match true [ECon name es] f st env uu uu); try solve_by_inversion.
  - rewrite H in Heqcall. inv Heqcall.
  - rewrite H in Heqcall. inv Heqcall.
  - inv H0. clear H0 Hind.
    simp eval_or_match in H.
    rewrite Heq1 in H; simpl in H.
    rewrite Heq0 in H; simpl in H.
    rewrite Heq in H; simpl in H.
    unfold build_conv in Heq.
    break_match; [break_match; [ break_match | ] | ]; do 2 eexists.
    inv Heq.
    inv H.
    reflexivity.
    inv Heq.
    inv Heq.
    inv H.
    reflexivity.
  - rewrite H in Heqcall. inv Heqcall.

  Unshelve.
  repeat constructor.
  repeat constructor.
Qed.

Theorem eval_or_match_app :
  forall (st : state nat) (env : sem_env val) (e : exp) (es : list exp) (f : nat),
    eval_or_match true (es ++ [e]) f st env uu uu =
      (let (st', r) := eval_or_match true es f st env uu uu in
       match r with
       | Rval vs =>
           let (st'', r0) := eval_or_match true [e] f st' env uu uu in
           match r0 with
           | Rval vs' => (st'', Rval (vs ++ vs'))
           | Rerr e0 => (st'', Rerr e0)
           end
       | Rerr e0 => (st', Rerr e0)
       end).
Proof.
  intros st env e es f.
  generalize dependent st.
  induction es; simpl; intro st.
  - simp eval_or_match.
    break_match.
    destruct r.
    reflexivity.
    reflexivity.
  - rewrite eval_or_match_cons.
    break_match.
    simp eval_or_match.
    break_match.
    rewrite eval_or_match_cons.
    rewrite Heqp.
    rewrite IHes.
    destruct (eval_or_match true es f s env uu uu); simpl.
    destruct r0.
    destruct (eval_or_match true [e] f s0 env uu uu).
    destruct r0.
    rewrite app_assoc.
    reflexivity.
    reflexivity.
    reflexivity.
    rewrite eval_or_match_cons.
    rewrite Heqp.
    reflexivity.
Qed.

Lemma eval_or_match_false_cons : forall p e pes' f st env matched_v err_v,
    eval_or_match false ((p, e) :: pes') f st env matched_v err_v =
      if NoDuplicates_dec string_dec (pat_bindings p [])
      then (match pmatch (sec env) (refs st) p matched_v [] with
            | Match env_v' =>
                eval_or_match true [e] f st
                              {| sev := nsAppend (alist_to_ns env_v') (sev env);
                                sec := (sec env) |} uu uu
            | No_match => eval_or_match false pes' f st env matched_v err_v
            | Match_type_error => (st, Rerr (Rabort Rtype_error))
            end)
      else (st, Rerr (Rabort Rtype_error)).
Proof.
  intros.
  simp eval_or_match.
  reflexivity.
Qed.

Equations length_helper (sel : bool) (es : if sel then list exp else list (pat * exp)) (vs : list val) : Prop := {
    length_helper true es vs  := length vs = length es;
    length_helper false es vs := length vs = 1;
  }.

Lemma eval_or_match_sel_length : forall sel es (f : nat) (st st' : state ST) (env : sem_env val) (vs : list val) match_v err_v,
    eval_or_match sel es f st env match_v err_v = (st', Rval vs) ->
    length_helper sel es vs.
Proof.
  intros.
  funelim (eval_or_match sel es f st env match_v err_v).
  - simp length_helper. simp eval_or_match in H. inv H. reflexivity.
  - simp length_helper. simp eval_or_match in H. inv H. reflexivity.
  - simp length_helper. simp eval_or_match in H. inv H. reflexivity.
  - simp length_helper. simp eval_or_match in H. inv H.
  - simp length_helper. simp eval_or_match in H0.
    break_match.
    apply H in H0.
    simp length_helper in H0.
    assumption.
    inv H0.
  - simp length_helper. rewrite H0 in Heqcall.
    apply H in Heqcall.
    simp length_helper in Heqcall.
  - simp length_helper. rewrite H0 in Heqcall.
    apply H in Heqcall.
    simp length_helper in Heqcall.
  - simp length_helper. rewrite H in Heqcall.
    inv Heqcall.
  - break_match.
    + break_match.
      -- simp eval_or_match in *.
         break_match.
         ++ break_match.
            ** apply H in H1.
               simp length_helper in *.
               assumption.
            ** inv Heqm.
            ** rewrite H1 in Heqcall.
               apply H in Heqcall.
               simp length_helper in *.
               assumption.
         ++ inv H1.
      -- rewrite H1 in Heqcall.
         inv Heqcall.
      -- rewrite H1 in Heqcall.
         eapply H0 in Heqcall.
         simp length_helper in *.
         assumption.
         reflexivity.
         reflexivity.
    + rewrite H1 in Heqcall. inv Heqcall.
  - apply Hind in Heq.
    simp length_helper in *.
    inv Heq.
  - rewrite H in Heqcall. inv Heqcall.
  - rewrite H in Heqcall. inv Heqcall.
  - apply Hind in Heq. rewrite H in Heqcall. inv Heqcall.
    simp length_helper in *.
  - rewrite H0 in Heqcall.
    apply H in Heqcall.
    simp length_helper in *.
  - rewrite H in Heqcall. inv Heqcall.
  - rewrite H in Heqcall. inv Heqcall.
  - rewrite H in Heqcall. inv Heqcall.
  - rewrite H in Heqcall. inv Heqcall. simp length_helper. reflexivity.
  - rewrite H in Heqcall. inv Heqcall.
  - rewrite H in Heqcall. inv Heqcall. simp length_helper. reflexivity.
  - rewrite H in Heqcall. inv Heqcall.
  - rewrite H in Heqcall. inv Heqcall.
  - rewrite H0 in Heqcall. apply H in Heqcall. simp length_helper in *.
  - rewrite H in Heqcall. inv Heqcall.
  - rewrite H in Heqcall. inv Heqcall.
    unfold list_result in H2.
    break_match; try inv H2.
    simp length_helper. reflexivity.
  - rewrite H in Heqcall. inv Heqcall.
  - apply Hind in Heq. simp length_helper in Heq. inv Heq.
  - rewrite H0 in Heqcall.
    break_match.
    apply H in Heqcall.
    simp length_helper in *.
    break_match.
    inv Heqcall.
    simp length_helper; reflexivity.
    inv Heqcall.
  - rewrite H in Heqcall. inv Heqcall.
  - apply Hind in Heq. simp length_helper in Heq. inv Heq.
  - break_match.
    rewrite H0 in Heqcall. inv Heqcall. simp length_helper; reflexivity.
    break_match.
    rewrite H0 in Heqcall.
    apply H in Heqcall.
    simp length_helper in *.
    rewrite H0 in Heqcall. inv Heqcall.
  - rewrite H in Heqcall. inv Heqcall.
  - rewrite H in Heqcall. inv Heqcall.
  - rewrite H1 in Heqcall. break_match.
    apply H in Heqcall.
    simp length_helper in *.
    break_match.
    apply H0 in Heqcall.
    simp length_helper in *.
    inv Heqcall.
  - rewrite H in Heqcall. inv Heqcall.
  - rewrite H in Heqcall. inv Heqcall.
  - apply Hind in Heq. simp length_helper in Heq. inv Heq.
  - rewrite H0 in Heqcall. apply H in Heqcall. simp length_helper in *.
  - rewrite H in Heqcall. inv Heqcall.
  - rewrite H in Heqcall. inv Heqcall.
  - rewrite H0 in Heqcall. apply H in Heqcall.
    simp length_helper in *.
  - rewrite H in Heqcall. inv Heqcall.
  - rewrite H in Heqcall. inv Heqcall.
  - rewrite H in Heqcall. inv Heqcall.
  - rewrite H in Heqcall. inv Heqcall.
  - rewrite H in Heqcall. inv Heqcall.
    apply Hind0 in Heq0.
    simp length_helper in Heq0. inv Heq0.
  - rewrite H in Heqcall. inv Heqcall.
    apply Hind in Heq. simp length_helper in *.
    simpl. rewrite Heq. reflexivity.
Qed.

Theorem eval_or_match_false_length : forall (es : list (pat * exp)) (f : nat) (st st' : state ST) (env : sem_env val) (vs : list val) match_v err_v,
    eval_or_match false es f st env match_v err_v = (st', Rval vs) -> length vs = 1.
Proof.
  intros.
  apply eval_or_match_sel_length in H.
  simp length_helper in H.
Qed.

Theorem eval_or_match_true_length : forall (es : list exp) (f : nat) (st st' : state ST) (env : sem_env val) (vs : list val),
    eval_or_match true es f st env uu uu = (st', Rval vs) -> length vs = length es.
Proof.
  intros.
  apply eval_or_match_sel_length in H.
  simp length_helper in H.
Qed.

Theorem eval_or_match_sing : forall (e : exp) (f : nat) (st st' : state ST) (env : sem_env val) (vs : list val),
    eval_or_match true [e] f st env uu uu = (st', Rval vs) -> exists v, vs = [v].
Proof.
  intros.
  apply eval_or_match_sel_length in H.
  simp length_helper in H.
  destruct vs; inv H.
  destruct vs; inv H.
  exists v. reflexivity.
Qed.

Theorem evaluate_decs_inc_fuel : forall (f : nat) (st st' : state ST) (env env' : sem_env val)
                                     (ds : list dec),
    evaluate_decs f st env ds = (st', Rval env') -> evaluate_decs (S f) st env ds = (st', Rval env').
Proof.
  intros.
  funelim (evaluate_decs f st env ds); simp evaluate_decs in *.
  - break_match.
    + remember (eval_or_match true [e] fuel st env uu uu). 
      destruct p0. destruct r.
      symmetry in Heqp0.
      apply (more_fuel_same_value fuel (S fuel)) in Heqp0; try lia.
      unfold evaluate in Heqp0.
      rewrite Heqp0.
      assumption.
      inv Heqp0.
      inv H.
    + inv H.
  - remember (evaluate_decs fuel st env ds). destruct p. rewrite Heqp in H. destruct r.
    symmetry in Heqp. apply H in Heqp.
    rewrite Heqp.
    assumption.
    inv H0.
  - remember (evaluate_decs fuel st env ds1). destruct p. rewrite Heqp in H. destruct r.
    symmetry in Heqp. apply H in Heqp.
    rewrite Heqp.
    eapply H0; try constructor.
    constructor.
    constructor.
    constructor.
    assumption.
    inv H1.
  - clear Heqcall.
    remember (evaluate_decs fuel st env [d1]). destruct p. rewrite Heqp in H. destruct r.
    symmetry in Heqp. apply H in Heqp.
    rewrite Heqp.
    remember (evaluate_decs fuel s (extend_dec_env s0 env) (d2 :: decl')). destruct p.
    destruct r.

    assert (copyHeqp0 : (s1, Rval s2) = evaluate_decs fuel s (extend_dec_env s0 env) (d2 :: decl')) by assumption.
    rewrite Heqp0 in Heqp0.
    eapply H0 in Heqp0.
    rewrite Heqp0.
    inv H1.
    apply H1.
    constructor.
    constructor.
    constructor.
    constructor.
    symmetry. assumption.
    reflexivity.
    inv H1.
    inv H1.
Qed.

Theorem evaluate_decs_more_fuel_same_value : forall (f f' : nat) (st st' : state ST) (env env' : sem_env val)
                                     (ds : list dec),
   f <= f' -> evaluate_decs f st env ds = (st', Rval env') -> evaluate_decs f' st env ds = (st', Rval env').
Proof.
  intros.
  induction H.
  assumption.
  apply evaluate_decs_inc_fuel.
  assumption.
Qed.
