Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Require Import StructTact.StructTactics.
Require Import Omega.

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


Inductive namespace_extended (M N V : Type) : namespace M N V -> namespace M N V -> Prop :=
| Reflexive_ns_extended : forall (ns : namespace M N V), namespace_extended M N V ns ns
| Extended_by_one : forall (ns0 ns1 : namespace M N V) (p : ident M N * V),
    namespace_extended M N V ns0 ns1 -> namespace_extended M N V ns0 (p::ns1).

Lemma empty_always_extendable :
  forall (M N V : Type) (ns : namespace M N V), namespace_extended M N V [] ns.
Proof.
  induction ns; constructor; assumption.
Qed.

Lemma idk :
  forall (M N V : Type) (ns0 ns1 : namespace M N V) (id : ident M N) (v : V),
    namespace_extended M N V ns0 ns1 ->
    namespace_extended M N V ((id,v)::ns0) ((id,v)::ns1).
Proof.
  induction ns0.
  intros ns1 id v H.
  constructor.
Abort.

Theorem namespace_extended_dec :
  forall (M N V : Type)
    (m_dec : forall (m0 m1 : M), {m0 = m1} + {m0 <> m1})
    (n_dec : forall (n0 n1 : N), {n0 = n1} + {n0 <> n1})
    (v_dec : forall (v0 v1 : V), {v0 = v1} + {v0 <> v1})
    (ns0 ns1 : namespace M N V),
    {namespace_extended M N V ns0 ns1} + {not (namespace_extended M N V ns0 ns1)}.
Proof.
  intros M N V m_dec n_dec v_dec.
  induction ns0; induction ns1.
  - left. constructor.
  - left. apply empty_always_extendable.
  - right. intro contra. inv contra.
  - destruct IHns1.
    + left. constructor. assumption.
    + destruct (list_eq_dec (pair_eq_dec _ _ (ident_eq_dec _ _ m_dec n_dec) v_dec) ns0 ns1).
      destruct (pair_eq_dec _ _ (ident_eq_dec _ _ m_dec n_dec) v_dec a a0).
      subst.
      left. constructor.
      right. intro contra.
      subst.
      inv contra. congruence.
      apply n. congruence.
      right. intro contra.
      inv contra. congruence.
      apply n. congruence.
Qed.

Definition environment_extended (env0 env1 : sem_env val) : Prop :=
  namespace_extended _ _ _ (sev env0) (sev env1) /\
  namespace_extended _ _ _ (sec env0) (sec env1).


Definition namespace_subset (M N V : Type) (ns0 ns1 : namespace M N V)
           (m_dec : forall (m0 m1 : M), {m0 = m1} + {m0 <> m1})
           (n_dec : forall (n0 n1 : N), {n0 = n1} + {n0 <> n1})
  : Prop :=
  forall (id : ident M N) (v : V),
    nsLookup (ident_eq_dec _ _ m_dec n_dec) id ns0 = Some v ->
    nsLookup (ident_eq_dec _ _ m_dec n_dec) id ns1 = Some v.

Definition env_subset (env0 env1 : sem_env val) : Prop :=
  namespace_subset _ _ _ (sev env0) (sev env1) string_dec string_dec /\
  namespace_subset _ _ _ (sec env0) (sec env1) string_dec string_dec.

Theorem namespace_subset_dec :
  forall (M N V : Type) (ns0 ns1 : namespace M N V)
    (m_dec : forall (m0 m1 : M), {m0 = m1} + {m0 <> m1})
    (n_dec : forall (n0 n1 : N), {n0 = n1} + {n0 <> n1}),
    {namespace_subset _ _ _ ns0 ns1 m_dec n_dec} + {not (namespace_subset _ _ _ ns0 ns1 m_dec n_dec)}.
Proof.
  intros M N V ns0 ns1 m_dec n_dec.
  generalize dependent ns1.
  induction ns0. intros ns1.
  - left. unfold namespace_subset.
    intros id v H. inv H.
  - destruct ns1.
    + right. unfold namespace_subset.
      intro contra.
      unfold nsLookup in contra. simpl in contra.






    Theorem env_subset_dec : forall (env0 env1 : sem_env val),
    {env_subset env0 env1} + {not (env_subset env0 env1)}.
Proof.




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

Lemma evaluate_single_step : forall (fuel' : nat) (st : state A) (env : sem_env val) (es : list exp),
    evaluate es (S fuel') st env =
    match es with
    | [] => (st, Rval [])
    | [EVar n] => match nsLookup ident_string_dec n (sev env) with
                 | Some v' => (st, Rval [v'])
                 | None => (st, Rerr (Rabort Rtype_error))
                 end
    | [EFun x e] => (st, Rval [Closure env x e])
    | [ECon cn es'] => if do_con_check (sec env) cn (length es')
                      then match evaluate (rev es') fuel' st env with
                           | (st', Rval vs) => match build_conv (sec env) cn (rev vs) with
                                              | Some v' => (st', Rval [v'])
                                              | None => (st', Rerr (Rabort Rtype_error))
                                              end
                           | res => res
                           end
                      else (st, Rerr (Rabort Rtype_error))

    | [EApp op es] => match (evaluate (rev es) fuel' st env) with
                     | (st', Rval vs) => if op_eq_dec op Opapp
                                        then match do_opapp (rev vs) with
                                             | Some (env', e) => evaluate [e] fuel' st' env'
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

    | [EMat e pes] => match (evaluate [e] fuel' st env) with
                     | (st', Rval (v'::vs')) =>
                       (fix evaluate_match (st : state A) (env : sem_env val) (v' : val)
                            (pes : list (pat * exp)) (err_v : val) : state A * result (list val) val :=
                          match pes with
                          | [] => (st, Rerr (Rraise err_v))
                          | (p,e)::pes' =>
                            if NoDuplicates_dec string_dec (pat_bindings p)
                            then match pmatch (sec env) (refs st) p v' [] with
                                 | Match env_v' => evaluate [e] fuel' st {| sev := nsAppend (alist_to_ns env_v') (sev env);
                                                                           sec := (sec env) |}
                                 | No_match => evaluate_match st env v' pes' err_v
                                 | Match_type_error => (st, Rerr (Rabort Rtype_error))
                                 end
                            else (st, Rerr (Rabort Rtype_error))
                          end)
                         st' env v' pes bind_exn_v
                     | res => res
                     end

    | [ELannot e l] => evaluate [e] fuel' st env

    | e::es' => match evaluate [e] fuel' st env with
              | (st', Rval vs) => (* This differs from lem semantics*)
                match evaluate es' fuel' st' env with
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

Definition evaluate_diverges {ffi' : Type} (st : state ffi') (env : sem_env val) (e : exp) : Prop :=
  forall (fuel : nat), exists (st' : state ffi'), evaluate [e] fuel st env = (st', Rerr (Rabort Rtimeout_error)).

(* Opaque evaluate. *)
Lemma exists_fuel_no_divergence : forall (st : state A) (env : sem_env val) (e : exp) (v : val),
    (exists (f : nat), evaluate [e] f st env = (st, Rval [v])) -> ~ evaluate_diverges st env e.
Proof.
  intros st env e.
  induction e;
    intros va H contra;
    inversion H as [f H']; specialize (contra f); inversion contra as [st' contra']; clear H; clear contra;
     rewrite H' in contra'; inversion contra'.
Qed.

Ltac inv H := inversion H; subst; clear H.

Lemma inc_fuel_same_res : forall (f : nat) (es : list exp) (st st' : state A)
                            (env : sem_env val) (res : result (list val) val),
    res <> Rerr (Rabort Rtimeout_error) ->
    evaluate es f st env = (st', res) ->
    evaluate es (S f) st env = (st', res).
Proof.
  induction f.
  destruct es.
  intros st st' env res Hres H.
  assumption.
  intros st st' env res Hres H.
  destruct e.
  - destruct es. simpl in *.
    destruct (do_con_check (sec env) c (Datatypes.length l));
      congruence.
    simpl in H; congruence.
  - destruct es; simpl in *; congruence.
  - destruct es; simpl in *; congruence.
  - destruct es; simpl in H; congruence.
  - destruct es; simpl in H; congruence.
  - destruct es; simpl in H; congruence.
  - intros es st st' env res Hres H.
    rewrite evaluate_single_step in *.
    destruct es. assumption.
    destruct e.
    + destruct es.
      destruct (do_con_check (sec env) c (Datatypes.length l)).
      destruct (evaluate (rev l) f st env) eqn:term0.
      destruct r.
      apply IHf in term0; try (congruence).
      rewrite term0.
      congruence.
      apply IHf in term0; try (congruence).
      rewrite term0.
      congruence.
      congruence.
      destruct (evaluate [ECon c l] f st env) eqn:term0.
      destruct r;
        apply IHf in term0; try (congruence);
          rewrite term0.
      destruct (evaluate (e :: es) f s env) eqn:term1.
      destruct r;
        apply IHf in term1; try (congruence);
          rewrite term1;
          congruence.
      congruence.
    + destruct es.
      congruence.
      destruct (evaluate [EVar i] f st env) eqn:term0.
      destruct r;
        apply IHf in term0; try (congruence);
        rewrite term0.
      destruct (evaluate (e :: es) f s env) eqn:term1.
      destruct r;
        apply IHf in term1; try (congruence);
        rewrite term1; congruence.
      congruence.
    + destruct es. congruence.
      destruct (evaluate [EFun v e] f st env) eqn:term0.
      destruct r;
        apply IHf in term0; try (congruence);
        rewrite term0.
      destruct (evaluate (e0 :: es) f s env) eqn:term1.
      destruct r;
        apply IHf in term1; try (congruence);
        rewrite term1; congruence.
      congruence.
    + destruct es.
      destruct (evaluate (rev l) f st env) eqn:term0.
      destruct r;
        apply IHf in term0; try (congruence);
          rewrite term0;
          try (congruence).
      destruct (op_eq_dec o Opapp); try (congruence).
      destruct (do_opapp (rev l0)); try (congruence).
      destruct p.
      apply IHf; congruence.
      destruct (evaluate [EApp o l] f st env) eqn:term0.
      destruct r;
        apply IHf in term0; try (congruence);
          rewrite term0;
          try (congruence).
      destruct (evaluate (e::es) f s env) eqn:term1.
      destruct r;
        apply IHf in term1; try (congruence);
          rewrite term1;
          try (congruence).
    + destruct es.
      destruct (evaluate [e] f st env) eqn:term0.
      destruct r;
        apply IHf in term0; try (congruence);
          rewrite term0;
          try (congruence).
      destruct l0; try (congruence).
      induction l. congruence.
      destruct a.
      destruct (NoDuplicates_dec string_dec (pat_bindings p)).
      destruct (pmatch (sec env) (refs s) p v []); try (congruence).
      apply IHl.
      congruence.
      apply IHf; assumption.
      congruence.
      destruct (evaluate [EMat e l] f st env) eqn:term0.
      destruct r;
        apply IHf in term0; try (congruence);
          rewrite term0;
          try (congruence).
      destruct (evaluate (e0::es) f s env) eqn:term1.
      destruct r;
        apply IHf in term1; try (congruence);
          rewrite term1;
          try (congruence).
    + destruct es.
      apply IHf; congruence.
      destruct (evaluate [ELannot e l] f st env) eqn:term0.
      destruct r;
        apply IHf in term0; try (congruence);
          rewrite term0;
          try (congruence).
      destruct (evaluate (e0::es) f s env) eqn:term1.
      destruct r;
        apply IHf in term1; try (congruence);
          rewrite term1;
          try (congruence).
Qed.

Lemma more_fuel_same_result : forall (f f' : nat) (st st' : state A) (env : sem_env val) (res : result (list val) val) (es : list exp),
    f <= f' ->
    res <> Rerr (Rabort Rtimeout_error) ->
    evaluate es f st env = (st', res) ->
    evaluate es f' st env = (st', res).
Proof.
  intros f f'. generalize dependent f.
  induction f';
    intros f st st' env res es H H1 contra;
    inv H; auto.
    apply inc_fuel_same_res; auto.
    apply IHf' with f; auto.
Qed.

Theorem ELannot_does_nothing : forall (e : exp) (l : locs) (f : nat) (st : state A) (env : sem_env val),
    evaluate [ELannot e l] (S f) st env = evaluate [e] f st env.
Proof.
  intros e l f st env.
  reflexivity.
Qed.

Theorem ELannot_does_nothing_ever : forall (e : exp) (l : locs) (f : nat) (st st' : state A)
                                      (env : sem_env val) (res : result (list val) val),
    evaluate [ELannot e l] f st env = (st', res) ->
    res <> Rerr (Rabort Rtimeout_error) ->
    evaluate [ELannot e l] f st env = evaluate [e] f st env.

Proof.
  intros e l f st st' env res H0 H1.
  destruct f.
  - simpl in H0; congruence.
  - simpl in *. rewrite H0. apply inc_fuel_same_res in H0. simpl in H0.
    rewrite H0. reflexivity. assumption.
Qed.

Opaque evaluate.
Ltac reduce_evaluate H :=
  rewrite evaluate_single_step in H; simpl in H.

Ltac more_fuel_same_result_quick :=
  match goal with
  | [ H0 : evaluate ?es ?f ?st ?env = (?st',?res), H1 : context[evaluate ?es ?f' ?st ?env] |- _ ] =>
    let H := fresh "H" in
    let Hass := fresh "Hass" in
    let Hass0 := fresh "Hass0" in
    assert (H : evaluate es f st env = (st',res)) by apply H0;
    assert (Hass : f <= f') by omega;
    assert (Hass0 : res <> (Rerr (Rabort Rtimeout_error))) by (simpl; congruence);
    apply (more_fuel_same_result f f' st st' env res es Hass Hass0) in H;
    rewrite H in H1;
    clear Hass Hass0 H
  end.

Ltac match_exp_same :=
  match goal with
  | [H : context[ match ?x with
                  | ECon _ _ => ?y
                  | EVar _   => ?y
                  | EFun _ _ => ?y
                  | EApp _ _ => ?y
                  | EMat _ _ => ?y
                  | ELannot _ _ => ?y
                  end] |- _ ] =>
    let Hass := fresh "Hass" in
    assert (Hass : match x with
                   | ECon _ _ => y
                   | EVar _   => y
                   | EFun _ _ => y
                   | EApp _ _ => y
                   | EMat _ _ => y
                   | ELannot _ _ => y
                   end
                   = y) by (destruct x; reflexivity);
    rewrite Hass in H; clear Hass
  end.

Theorem plus_vs_cake_plus : forall (m n t f : nat) (m_exp n_exp : exp) (m_val n_val m_n_val : val) (env : sem_env val),
    environment_extended my_env env ->
    evaluate [m_exp] f my_st my_env = (my_st, Rval [m_val]) ->
    evaluate [n_exp] f my_st my_env = (my_st, Rval [n_val]) ->
    nat_rel_cake_nat t m m_val ->
    nat_rel_cake_nat t n n_val ->
    evaluate [(EApp (Opapp) ((EApp (Opapp) ((EVar (Short ("plus"%string)))::m_exp::nil))::n_exp::nil))]
             f my_st my_env =
    (my_st, Rval [m_n_val]) ->
    nat_rel_cake_nat t (m+n) m_n_val.
Proof.
  Opaque evaluate.
  intros m n t f m_exp n_exp m_val n_val m_n_val env Henv Hm Hn Hrelm Hreln.
  generalize dependent Hn.
  generalize dependent Hm.
  generalize dependent Henv.
  generalize dependent env.
  generalize dependent m_n_val.
  generalize dependent f.
  generalize dependent m_exp.
  generalize dependent n_exp.
  induction Hreln.
  induction Hrelm.
  intros n_exp m_exp f m_n_val env Henv Hm Hn Hmn.
  simpl in *.
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  reduce_evaluate Hmn.
  break_let.
  reduce_evaluate Heqp.
  more_fuel_same_result_quick.
  match_exp_same.
  break_let.
  reduce_evaluate Heqp0.
  break_let. reduce_evaluate Heqp1.
  more_fuel_same_result_quick.
  match_exp_same.
  break_let.
  reduce_evaluate Heqp2.
  inv Heqp2.
  inv Heqp1.
  simpl in Heqp0.
  reduce_evaluate Heqp0.
  inv Heqp0.
  inv Heqp.
  simpl in Hmn.
  reduce_evaluate Hmn.
  reduce_evaluate Hmn.
  break_let.
  reduce_evaluate Heqp.
  reduce_evaluate Heqp.
  inv Heqp.
  simpl in Hmn.
  destruct t. (* Need better way to do this. This is manual typechecking *)
  (* case 0 *)
  simpl in *.
  reduce_evaluate Hmn.
  reduce_evaluate Hmn.
  inv Hmn.
  constructor.
  (*case S t *)
  simpl in Hmn.
  inv Hmn.

  intros n_exp m_exp f m_n_val env Henv Hm Hn Hmn.
  rewrite <- plus_n_O.
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  apply inc_fuel_same_res in Hmn; try (congruence).
  reduce_evaluate Hmn.
  break_let.
  reduce_evaluate Heqp.
  more_fuel_same_result_quick.
  match_exp_same.
  break_let.
  reduce_evaluate Heqp0.
  break_let. reduce_evaluate Heqp1.
  more_fuel_same_result_quick.
  match_exp_same.
  break_let.
  reduce_evaluate Heqp2.
  inv Heqp2.
  inv Heqp1.
  simpl in Heqp0.
  reduce_evaluate Heqp0.
  inv Heqp0.
  inv Heqp.
  simpl in Hmn.
  reduce_evaluate Hmn.
  reduce_evaluate Hmn.
  break_let.
  reduce_evaluate Heqp.
  reduce_evaluate Heqp.
  inv Heqp.
  simpl in Hmn.

  destruct t. (* Need better way to do this. This is manual typechecking *)
  (* case 0 *)
  simpl in *.
  (* Start from here I think *)
  (* NIGHTMARE ZONE ALERT *)
  (* Are we manually proving n + 0 = n inside CakeML Syntax? *)
  reduce_evaluate Hmn.
  reduce_evaluate Hmn.
  break_let.
  reduce_evaluate Heqp.
  break_let.
  reduce_evaluate Heqp0.
  break_let.
  reduce_evaluate Heqp1.
  reduce_evaluate Heqp1.
  inv Heqp1.
  break_let.
  reduce_evaluate Heqp1.
  reduce_evaluate Heqp1.
  break_let.
  reduce_evaluate Heqp2.
  break_let.
  reduce_evaluate Heqp3.
  reduce_evaluate Heqp3.
  inv Heqp3.
  break_let.
  reduce_evaluate Heqp3.
  reduce_evaluate Heqp3.
  inv Heqp3.
  inv Heqp2.
  simpl in *.
  reduce_evaluate Heqp1.
  inv Heqp1.
  inv Heqp0.
  simpl in *.
  reduce_evaluate Heqp.
  Opaque stamp_eq_dec.
  reduce_evaluate Heqp.
  break_let.
  reduce_evaluate Heqp0.
  reduce_evaluate Heqp0.
  inv Heqp0.
  destruct r.
  inv Hmn.
  break_match.
  break_match.
  inv Heqp.
  inv Heqp.
  reduce_evaluate Heqp.
  reduce_evaluate Heqp.
  break_let.
  reduce_evaluate Heqp0.
  break_let.
  reduce_evaluate Heqp1.
  break_let.
  reduce_evaluate Heqp2.
  reduce_evaluate Heqp2.
  simpl in Heqp2.
  destruct nsLookup.
  inv Heqp2.
  break_let.
  reduce_evaluate Heqp2.
  reduce_evaluate Heqp2.
  break_let.
  reduce_evaluate Heqp3.
  break_let.
  reduce_evaluate Heqp4.
  reduce_evaluate Heqp4.
  simpl in *.
  destruct nsLookup.
  inv Heqp4.
  break_let.
  reduce_evaluate Heqp4.
  reduce_evaluate Heqp4.
  simpl in Heqp4.
  (* At this point we need guaruntees about our new environment. In this case a : alist varN val *)
  (* We should be asking what typechecking buys us here *)
  (* We should be able to figure out that 'a' is either an empty list or [("xp", v')] we then know that 'vs' = [] or [v']  *)
  destruct prev.
  inv Heqm0.
  destruct o.
  destruct (stamp_eq_dec (TypeStamp "S" 0) s4).
  destruct l0.
  inv Heqm0.
  destruct l0.
  inv Heqm0.
  simpl in Heqp4.
  inv Heqp4.
  inv Heqp3.
  simpl in Heqp2.
  reduce_evaluate Heqp2.
  inv Heqp2.
  inv Heqp1.
  simpl in Heqp0.
