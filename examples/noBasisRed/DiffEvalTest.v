Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Require Import StructTact.StructTactics.
Require Import Omega.
Require Import Coq.Logic.Eqdep_dec.

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

(* Theorem namespace_subset_dec : *)
(*   forall (M N V : Type) (ns0 ns1 : namespace M N V) *)
(*     (m_dec : forall (m0 m1 : M), {m0 = m1} + {m0 <> m1}) *)
(*     (n_dec : forall (n0 n1 : N), {n0 = n1} + {n0 <> n1}), *)
(*     {namespace_subset _ _ _ ns0 ns1 m_dec n_dec} + {not (namespace_subset _ _ _ ns0 ns1 m_dec n_dec)}. *)
(* Proof. *)
(*   intros M N V ns0 ns1 m_dec n_dec. *)
(*   generalize dependent ns1. *)
(*   induction ns0. intros ns1. *)
(*   - left. unfold namespace_subset. *)
(*     intros id v H. inv H. *)
(*   - destruct ns1. *)
(*     + right. unfold namespace_subset. *)
(*       intro contra. *)
(*       unfold nsLookup in contra. simpl in contra. *)

Inductive nat_rel_cake_nat (typestamp : nat) : nat -> val -> Prop :=
| zero_rel : nat_rel_cake_nat typestamp 0 (Conv (Some (TypeStamp "O" typestamp)) [])
| suc_rel  : forall (n : nat) (prev : val), nat_rel_cake_nat typestamp n prev -> nat_rel_cake_nat typestamp (S n) (Conv (Some (TypeStamp "S" typestamp)) [prev]).

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

Print state.

Definition evaluate_diverges {ffi' : Type} (st : state ffi') (env : sem_env val) (e : exp) : Prop :=
  forall (fuel : nat), exists (st' : state ffi'), evaluate [e] fuel st env = (st', Rerr (Rabort Rtimeout_error)).

Lemma exists_fuel_no_divergence : forall (st : state A) (env : sem_env val) (e : exp) (v : val),
    (exists (f : nat), evaluate [e] f st env = (st, Rval [v])) -> ~ evaluate_diverges st env e.
Proof.
  intros st env e.
  induction e;
    intros va H contra;
    inversion H as [f H']; specialize (contra f); inversion contra as [st' contra']; clear H; clear contra;
     rewrite H' in contra'; inversion contra'.
Qed.

Require Import Equations.Equations.

Ltac inv H := inversion H; subst; clear H.
Lemma Forall''_app : forall (T : Type) (P : T -> Type) (l : list T) (a : T), Forall'' P l -> P a -> Forall'' P (l ++ [a]).
  intros.
  induction l.
  constructor.
  assumption.
  assumption.
  inv X.
  constructor.
  assumption.
  apply IHl.
  assumption.
Qed.

Lemma Forall''_rev : forall (T : Type) (P : T -> Type) (l : list T),
    Forall'' P l -> Forall'' P (rev l).
  intros.
  induction l.
  constructor.
  inv X.
  simpl.
  apply Forall''_app; auto.
Qed.

Lemma eval_or_match_sing : forall (e : exp) (f : nat) (st st' : state A) (env : sem_env val) (vs : list val),
    eval_or_match true [e] f st env uu uu = (st', Rval vs) -> exists (v : val), vs = [v].
Proof.
  intros e f.
  revert e.
  induction f; induction e; intros.
  - unfold evaluate in H. simp eval_or_match in H.
    destruct (do_con_check (sec env) o (Datatypes.length l)).
    break_let.
    destruct r.
    destruct (build_conv (sec env) o (rev l0)); inv H; eauto.
    inv H.
    inv H.

 - unfold evaluate in H. simp eval_or_match in H. simp eval_or_match in H.
   destruct (nsLookup ident_string_dec i (sev env)); inv H; eauto.

 - unfold evaluate in H. simp eval_or_match in H. simp eval_or_match in H.
   inv H.
   eauto.

 - unfold evaluate in H. simp eval_or_match in H. simp eval_or_match in H. inv H.

 - unfold evaluate in H. simp eval_or_match in H.
   induction X.
   break_let.
   simp eval_or_match in H.
   destruct r. apply IHe in Heqp.
   destruct Heqp.
   rewrite H0 in *.
   simp eval_or_match in H.
   inv H.
   inv H.
   break_let.
   destruct r.
   apply IHe in Heqp0.
   destruct Heqp0.
   rewrite H0 in *. clear H0.
   destruct x.
   simpl in *.
   simp eval_or_match in H.
   break_if.
   break_match.
   apply IHX in H.
   apply H.
   inv H.
   apply p in H.
   apply H.
   inv H.
   inv H.

 - unfold evaluate in H. simp eval_or_match in H.

 - unfold evaluate in H. simp eval_or_match in H.
    destruct (do_con_check (sec env) o (Datatypes.length l)).
    break_let.
    destruct r.
    destruct (build_conv (sec env) o (rev l0)); inv H; eauto.
    inv H.
    inv H.

 - unfold evaluate in H. simp eval_or_match in H.
   destruct (nsLookup ident_string_dec i (sev env)).
   inv H. exists v. reflexivity.
   inv H.

 - unfold evaluate in H. simp eval_or_match in H.
   inv H. exists (Closure env v e). reflexivity.

 - unfold evaluate in H. simp eval_or_match in H.
   break_let.
   apply Forall''_rev in X.
   induction X.
   simp eval_or_match in Heqp.
   inv Heqp.
   break_if.
   simpl in H.
   inv H.
   simpl in *.
   inv H.
   destruct r.
   break_if.
   break_match.
   break_let.
   apply IHf in H.
   apply H.
   inv H.
   break_match.
   break_let.
   break_let.
   inv H.
   destruct r.
   simpl in *.
   inv H2.
   exists v. reflexivity.
   inv H2.
   inv H.
   inv H.

 - unfold evaluate in H. simp eval_or_match in H.
   break_let.
   destruct r.
   apply IHe in Heqp.
   destruct Heqp.
   rewrite H0 in *.
   induction X.
   simp eval_or_match in H.
   inv H.
   destruct x0.
   simp eval_or_match in *.
   break_if.
   break_match.
   apply IHX.
   apply H.
   inv H.
   apply p in H.
   apply H.
   inv H.
   inv H.

 - unfold evaluate in H. simp eval_or_match in H.
Qed.

Theorem eval_or_match_cons : forall (st : state A) (env : sem_env val) (e : exp) (es : list exp) (f : nat),
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
  unfold evaluate.
  intros. revert e st.
  destruct es; intros; simpl.
  destruct (eval_or_match true [e] f st env uu uu).
  destruct r.
  simp eval_or_match.
  rewrite app_nil_r.
  congruence.
  congruence.
  simp eval_or_match.
  destruct (eval_or_match true [e0] f st env uu uu) eqn:eval1.
  destruct r.
  apply eval_or_match_sing in eval1.
  destruct eval1. rewrite H. simpl.
  congruence.
  congruence.
Qed.

Theorem evaluate_cons : forall (st : state A) (env : sem_env val) (e : exp) (es : list exp) (f : nat),
   evaluate (e::es) f st env =
     match evaluate [e] f st env with
     | (st', Rval vs) =>
      match evaluate es f st' env with
       | (st'', Rval vs') => (st'', Rval (vs++vs'))
       | err => err
      end
     | err => err
     end.
Proof.
  unfold evaluate.
  apply eval_or_match_cons.
Qed.

Theorem eval_or_match_app : forall (st : state A) env xs ys f,
   eval_or_match true (xs ++ ys) f st env uu uu =
     match eval_or_match true xs f st env uu uu with
     | (st', Rval vs) =>
       match eval_or_match true ys f st' env uu uu with
       | (s'', Rval vs') => (s'', Rval (vs++vs'))
       | err => err
       end
     | err => err
     end.
Proof.
  intros. revert ys st.
  induction xs; intros. simpl.
  unfold evaluate.
  simp eval_or_match.
  destruct (eval_or_match true ys f st env uu uu).
  destruct r; simpl; congruence.
  rewrite eval_or_match_cons.
  simpl.
  rewrite eval_or_match_cons.
  destruct (eval_or_match true [a] f st env uu uu).
  destruct r.
  rewrite IHxs.
  destruct (eval_or_match true xs f s env uu uu ).
  destruct r.
  destruct (eval_or_match true ys f s0 env uu uu).
  destruct r.
  rewrite app_assoc_reverse.
  congruence.
  congruence.
  congruence.
  congruence.
Qed.

Theorem evaluate_app : forall (st : state A) env xs ys f,
   evaluate (xs ++ ys) f st env =
     match evaluate xs f st env with
     | (st', Rval vs) =>
       match evaluate ys f st' env with
       | (s'', Rval vs') => (s'', Rval (vs++vs'))
       | err => err
       end
     | err => err
     end.
Proof.
  unfold evaluate; apply eval_or_match_app.
Qed.

(* Lemma eval_or_match_sing : forall fuel e env (st : state A), *)
(*   eval_or_match true [e] fuel st env uu uu = *)
(*   match e with *)
(*   | EVar n => match nsLookup ident_string_dec n (sev env) with *)
(*              | Some v' => (st, Rval [v']) *)
(*              | None => (st, Rerr (Rabort Rtype_error)) *)
(*              end *)
(*   | ECon cn es' => if do_con_check (sec env) cn (length es') *)
(*                   then match eval_or_match true (rev es') fuel st env uu uu with *)
(*                        | (st', Rval vs) => *)
(*                          match build_conv (sec env) cn (rev vs) with *)
(*                          | Some v' => (st', Rval [v']) *)
(*                          | None => (st', Rerr (Rabort Rtype_error)) *)
(*                          end *)
(*                        | res => res *)
(*                        end *)
(*                   else (st, Rerr (Rabort Rtype_error)) *)
(*   | EFun x e => (st, Rval [Closure env x e]) *)
(*   | EApp op es => match fuel with *)
(*                  | 0 => (st, Rerr (Rabort Rtimeout_error)) *)
(*                  | S fuel' => match eval_or_match true (rev es) fuel' st env uu uu with *)
(*                           | (st', Rval vs) => if op_eq_dec op Opapp *)
(*                                              then match do_opapp (rev vs) with *)
(*                                                   | Some (env', e) => eval_or_match true [e] fuel' st' env' uu uu *)
(*                                                   | None => (st', Rerr (Rabort Rtype_error)) *)
(*                                                   end *)
(*                                              else match do_app _ (refs st', ffi st') op (rev vs) with *)
(*                                                   | Some ((refs, ffi), r) => ({| refs := refs; *)
(*                                                                                 ffi  := ffi; *)
(*                                                                                 clock := clock st'; *)
(*                                                                                 next_type_stamp := next_type_stamp st' ; *)
(*                                                                                 next_exn_stamp := next_exn_stamp st' *)
(*                                                                              |}, *)
(*                                                                              list_result r) *)
(*                                                   | None => (st', Rerr (Rabort Rtype_error)) *)
(*                                                   end *)
(*                           | res => res *)
(*                           end *)
(*                  end *)
(*   | EMat e pes => match eval_or_match true [e] fuel st env uu uu with *)
(*                  | (st', Rval (v'::vs')) => *)
(*                    eval_or_match false pes fuel st' env v' bind_exn_v *)

(*                  | res => res *)
(*                  end *)
(*   | ELannot e l => eval_or_match true [e] fuel st env uu uu *)
(*   end. *)
(* Proof. *)
(*   induction e; *)
(*   intros; *)
(*   simp eval_or_match; *)
(*   try (reflexivity). *)
(*   destruct fuel; simp eval_or_match; reflexivity. *)
(* Qed. *)

(* Lemma Forall''_image A B : forall (f : A -> B) l, *)
(*   Forall'' (fun y => exists x, y = f x) l -> exists l', l = map f l'. *)
(*   intros. *)
(*   induction X. *)
(*   exists []. reflexivity. *)
(*   destruct p. *)
(*   rewrite H; clear H. *)
(*   destruct IHX. *)
(*   exists (x0::x1). *)
(*   simpl. *)
(*   rewrite <- H. reflexivity. *)
(* Qed. *)

(* Lemma eval_sing_inc_fuel : forall (f : nat) (e : exp) (st st' : state A) *)
(*                             (env : sem_env val) (res : result (list val) val), *)
(*     res <> Rerr (Rabort Rtimeout_error) -> *)
(*     evaluate [e] f st env = (st', res) -> *)
(*     evaluate [e] (S f) st env = (st', res). *)
(* Proof. *)
(*   induction f. *)
(*   intros. *)
(*   unfold evaluate in *. *)
(*   funelim (eval_or_match true [e] 0 st env uu uu). *)
(*   apply H; try (assumption). *)
(*   unfold eq_rect. *)
(*   intros. simpl. rewrite H1. *)
(*   Check eval_or_match_elim. *)
(*   Check eq_rect. *)
(* Check eval_or_match_elim. *)
Check eq_refl.

(* Axiom USOP : forall (U : Type) (x y:U) (p1 p2:x = y), p1 = p2. *)
Require Import Program.

(* Lemma eq_match : forall (X Y : Type) (Z : X -> Type) (y : Y) (z : Z) (H : X = X), *)
(*     match H in (_ = h) return Z h with *)
(*     | eq_refl => z *)
(*     end = z. *)
(* Proof. *)
(*   intros. *)
(*   dependent destruction H. *)
(*   reflexivity. *)
(* Qed. *)

Lemma eval_or_match_inc_fuel_val : forall (f : nat) (sel : bool)
                                     (es : if sel then list exp else list (pat * exp)) (st st' : state A)
                                     (env : sem_env val) (match_v err_v : val) (vs : list val),
    eval_or_match sel es f st env match_v err_v = (st', Rval vs) ->
    eval_or_match sel es (S f) st env match_v err_v = (st', Rval vs).
Proof.
  intros.
  funelim (eval_or_match sel es f st env match_v err_v).
  - simp eval_or_match in *.
  - simp eval_or_match in *.
    break_if.
    + destruct (eval_or_match true (rev l) fuel st env uu uu) eqn:eval1.
      rewrite <- eval1 in H.
      destruct r.
      * apply H in eval1.
        rewrite eval1.
        break_match.
        assumption.
        inv Heqcall.
        inv H0.
      * inv Heqcall.
        inv H0.
    + inv Heqcall.
      inv H0.
  - simp eval_or_match. rewrite Heqcall. assumption.
  - simp eval_or_match. rewrite Heqcall. assumption.
  - rewrite <- Heqcall in H. inv H.
  - simp eval_or_match in *.
    destruct (eval_or_match true (rev l0) n st env uu uu) eqn:eval1.
    destruct r.
    * rewrite <- eval1 in H.
      apply H in eval1.
      rewrite eval1.
      break_if.
      + break_match.
        -- break_let.
           simpl in H0.
           unfold eq_rect in Heqcall. simpl in *.
           remember (@sigmaI Type (fun x => sigma (fun b : bool => sigma (fun l : if b then list exp else list (pat * exp) => sigma (fun n => sigma (fun st : state x => sigma (fun sem => sigma (fun v1 => val ))))))) A
                 (@sigmaI bool (fun b : bool => sigma (fun l : if b then list exp else list (pat * exp) => sigma (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val )))))) true
                          (@sigmaI (list exp) (fun l => sigma (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val ))))) [e0]
                                   (@sigmaI nat (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val )))) n
                                            (@sigmaI (state A) (fun st => sigma (fun sem => sigma (fun v1 => val ))) s
                                                     (@sigmaI (sem_env val) (fun sem => sigma (fun v1 => val )) s0
                                                              (@sigmaI val (fun v1 => val) uu uu)))))))
             as ididit.
           assert (ididit = ididit).
           auto.
           rewrite Heqididit in H2.
           specialize (H0 s (Rval vs) vs e p s0 e0 n true [e0] s st' s0 uu uu vs H1 H2).
           apply H0.
           unfold eq_rect.
           dependent destruction H2.
           reflexivity.
        -- inv H1.
      + break_match. auto.
        inv H1.
    * inv H1.
  - simp eval_or_match in *.
    destruct (eval_or_match true [e0] fuel st env uu uu) eqn:eval1.
    rewrite <- eval1 in H.
    destruct r.
    apply H in eval1.
    rewrite eval1.
    destruct l.
    assumption.
    remember (@sigmaI Type (fun x => sigma (fun b : bool => sigma (fun l : if b then list exp else list (pat * exp) => sigma (fun n => sigma (fun st : state x => sigma (fun sem => sigma (fun v1 => val ))))))) A
                      (@sigmaI bool (fun b : bool => sigma (fun l : if b then list exp else list (pat * exp) => sigma (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val )))))) false
                               (@sigmaI (list (pat * exp)) (fun l => sigma (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val ))))) l1
                                        (@sigmaI nat (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val )))) fuel
                                                 (@sigmaI (state A) (fun st => sigma (fun sem => sigma (fun v1 => val ))) s
                                                          (@sigmaI (sem_env val) (fun sem => sigma (fun v1 => val )) env
                                                                   (@sigmaI val (fun v1 => val) v bind_exn_v)))))))
             as ididit.
           assert (ididit = ididit).
           auto.
           rewrite Heqididit in H2.

           specialize (H0 s (Rval vs) vs v vs fuel false l1 s st' env v bind_exn_v vs H1 H2).
           apply H0.
           unfold eq_rect.
           dependent destruction H2.
           reflexivity.
           inv H1.
  - simp eval_or_match in *.
  - simp eval_or_match in *.
    destruct (eval_or_match true [e] fuel st env uu uu) eqn:eval1.
    rewrite <- eval1 in H.
    destruct r.
    apply H in eval1.
    rewrite eval1.
    destruct (eval_or_match true (e0::l) fuel s env uu uu) eqn:eval2.
    destruct r.
    remember (@sigmaI Type (fun x => sigma (fun b : bool => sigma (fun l : if b then list exp else list (pat * exp) => sigma (fun n => sigma (fun st : state x => sigma (fun sem => sigma (fun v1 => val ))))))) A
                      (@sigmaI bool (fun b : bool => sigma (fun l : if b then list exp else list (pat * exp) => sigma (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val )))))) true
                               (@sigmaI (list exp) (fun l => sigma (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val ))))) (e0::l)
                                        (@sigmaI nat (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val )))) fuel
                                                 (@sigmaI (state A) (fun st => sigma (fun sem => sigma (fun v1 => val ))) s
                                                          (@sigmaI (sem_env val) (fun sem => sigma (fun v1 => val )) env
                                                                   (@sigmaI val (fun v1 => val) uu uu)))))))
             as ididit.
    assert (ididit = ididit).
    auto.
    rewrite Heqididit in H2.
    specialize (H0 s (Rval vs) vs fuel true (e0::l) s s0 env uu uu l1 eval2 H2).
    unfold eq_rect in H0.
    assert (eval_or_match true (e0 :: l) fuel s env uu uu =
            eval_or_match true (e0 :: l) fuel s env uu uu) by congruence.
    rewrite H0. assumption.
    dependent destruction H2.
    reflexivity.
    congruence.
    inv H1.
  - simp eval_or_match in *.
  - simp eval_or_match in *.
    clear Heqcall.
    break_match.
    break_match.
    apply H.
    assumption.
    assumption.
    inv H1.

    remember (@sigmaI Type (fun x => sigma (fun b : bool => sigma (fun l : if b then list exp else list (pat * exp) => sigma (fun n => sigma (fun st : state x => sigma (fun sem => sigma (fun v1 => val ))))))) A
                      (@sigmaI bool (fun b : bool => sigma (fun l : if b then list exp else list (pat * exp) => sigma (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val )))))) true
                               (@sigmaI (list exp) (fun l => sigma (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val ))))) [e]
                                        (@sigmaI nat (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val )))) fuel
                                                 (@sigmaI (state A) (fun st => sigma (fun sem => sigma (fun v1 => val ))) st
                                                          (@sigmaI (sem_env val) (fun sem => sigma (fun v1 => val )) {| sev := nsAppend (alist_to_ns a) (sev env); sec := sec env |}
                                                                   (@sigmaI val (fun v1 => val) uu uu)))))))
             as ididit.
    assert (ididit = ididit).
    auto.
    rewrite Heqididit in H2.
    unfold eq_rect.
    specialize (H0 n a fuel true [e] st st' {| sev := nsAppend (alist_to_ns a) (sev env); sec := sec env |} uu uu vs H1 H2).
    apply H0.
    unfold eq_rect.
    dependent destruction H2; reflexivity.
    congruence.
Qed.

Lemma eval_or_match_inc_fuel_res : forall (f : nat) (sel : bool)
                                     (es : if sel then list exp else list (pat * exp)) (st st' : state A)
                                     (env : sem_env val) (match_v err_v : val) (res : result (list val) val),
    res <> Rerr (Rabort Rtimeout_error) ->
    eval_or_match sel es f st env match_v err_v = (st', res) ->
    eval_or_match sel es (S f) st env match_v err_v = (st', res).
Proof.
  intros.
  funelim (eval_or_match sel es f st env match_v err_v).
  - simp eval_or_match in *.
  - simp eval_or_match in *.
    clear Heqcall.
    break_match.
    destruct (eval_or_match true (rev l) fuel st env uu uu) eqn:eval1.
    rewrite <- eval1 in H.
    apply H in eval1.
    rewrite eval1.
    destruct r.
    break_match; assumption.
    inv H1.
    congruence.
    destruct r.
    congruence.
    congruence.
    congruence.
  - simp eval_or_match in *.
  - simp eval_or_match in *.
  - simp eval_or_match in *. congruence.
  - simp eval_or_match in *.
    destruct (eval_or_match true (rev l0) n st env uu uu) eqn:eval1.
    rewrite <- eval1 in H.
    apply H in eval1.
    rewrite eval1.
    break_match.
    + break_if.
      * break_match.
        -- break_let.
           simpl in H0.
           remember (@sigmaI Type (fun x => sigma (fun b : bool => sigma (fun l : if b then list exp else list (pat * exp) => sigma (fun n => sigma (fun st : state x => sigma (fun sem => sigma (fun v1 => val ))))))) A
                 (@sigmaI bool (fun b : bool => sigma (fun l : if b then list exp else list (pat * exp) => sigma (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val )))))) true
                          (@sigmaI (list exp) (fun l => sigma (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val ))))) [e0]
                                   (@sigmaI nat (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val )))) n
                                            (@sigmaI (state A) (fun st => sigma (fun sem => sigma (fun v1 => val ))) s
                                                     (@sigmaI (sem_env val) (fun sem => sigma (fun v1 => val )) s0
                                                              (@sigmaI val (fun v1 => val) uu uu)))))))
             as ididit.
           assert (ididit = ididit).
           auto.
           rewrite Heqididit in H3.

           Check H0.
           specialize (H0 s res l e p s0 e0 n true [e0] s st' s0 uu uu res H1 H2 H3).
           apply H0.
           unfold eq_rect.
           dependent destruction H3. reflexivity.
        -- congruence.
      * break_match; auto.
    + congruence.
    + destruct r; congruence.
  - simp eval_or_match in *.
    destruct (eval_or_match true [e0] fuel st env uu uu) eqn:eval1.
    rewrite <- eval1 in H.
    apply H in eval1.
    rewrite eval1.
    destruct r; auto.
    destruct l; auto.
    remember (@sigmaI Type (fun x => sigma (fun b : bool => sigma (fun l : if b then list exp else list (pat * exp) => sigma (fun n => sigma (fun st : state x => sigma (fun sem => sigma (fun v1 => val ))))))) A
                      (@sigmaI bool (fun b : bool => sigma (fun l : if b then list exp else list (pat * exp) => sigma (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val )))))) false
                               (@sigmaI (list (pat * exp)) (fun l => sigma (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val ))))) l1
                                        (@sigmaI nat (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val )))) fuel
                                                 (@sigmaI (state A) (fun st => sigma (fun sem => sigma (fun v1 => val ))) s
                                                          (@sigmaI (sem_env val) (fun sem => sigma (fun v1 => val )) env
                                                                   (@sigmaI val (fun v1 => val) v bind_exn_v)))))))
             as ididit.
    assert (ididit = ididit).
    auto.
    rewrite Heqididit in H3.
    Check H0.
    specialize (H0 s res l v l fuel false l1 s st' env v bind_exn_v res H1 H2 H3).
    apply H0.
    unfold eq_rect.
    dependent destruction H3.
    reflexivity.
    destruct r; congruence.
  - simp eval_or_match in *.
  - simp eval_or_match in *.
    clear Heqcall.
    destruct (eval_or_match true [e] fuel st env uu uu) eqn:eval1.
    rewrite <- eval1 in H.
    apply H in eval1.
    rewrite eval1.
    remember (@sigmaI Type (fun x => sigma (fun b : bool => sigma (fun l : if b then list exp else list (pat * exp) => sigma (fun n => sigma (fun st : state x => sigma (fun sem => sigma (fun v1 => val ))))))) A
                      (@sigmaI bool (fun b : bool => sigma (fun l : if b then list exp else list (pat * exp) => sigma (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val )))))) true
                               (@sigmaI (list exp) (fun l => sigma (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val ))))) (e0::l)
                                        (@sigmaI nat (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val )))) fuel
                                                 (@sigmaI (state A) (fun st => sigma (fun sem => sigma (fun v1 => val ))) s
                                                          (@sigmaI (sem_env val) (fun sem => sigma (fun v1 => val )) env
                                                                   (@sigmaI val (fun v1 => val) uu uu)))))))
      as ididit.
    assert (ididit = ididit) by auto.
    rewrite Heqididit in H3.
    destruct r.
    + destruct (eval_or_match true (e0::l) fuel s env uu uu) eqn:eval2.
      destruct r.
      * destruct l0.
        -- assert (HneqValErr : ((Rval l1 : result (list val) val) <> Rerr (Rabort Rtimeout_error))) by congruence.
        specialize (H0 s (Rval l1) l1 fuel true (e0::l) s s0 env uu uu (Rval l1) HneqValErr eval2 H3).
        unfold eq_rect in H0.
        dependent destruction H3.
        rewrite H0; congruence.
        -- assert (HneqValErr : ((Rval l1 : result (list val) val) <> Rerr (Rabort Rtimeout_error))) by congruence.
           specialize (H0 s (Rval (l1)) l1 fuel true (e0::l) s s0 env uu uu (Rval (l1)) HneqValErr eval2 H3).
           unfold eq_rect in H0.
           dependent destruction H3.
           rewrite H0; congruence.
        * inv H2.
          specialize (H0 s (Rerr e1) l0 fuel true (e0::l) s st' env uu uu (Rerr e1) H1 eval2 H3).
          unfold eq_rect in H0.
          dependent destruction H3.
          rewrite H0; congruence.
    + congruence.
    + destruct r; congruence.
  - simp eval_or_match in *.
  - simp eval_or_match in *.
    break_if.
    + break_match.
      * apply H; assumption.
      * congruence.
      * remember (@sigmaI Type (fun x => sigma (fun b : bool => sigma (fun l : if b then list exp else list (pat * exp) => sigma (fun n => sigma (fun st : state x => sigma (fun sem => sigma (fun v1 => val ))))))) A
                          (@sigmaI bool (fun b : bool => sigma (fun l : if b then list exp else list (pat * exp) => sigma (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val )))))) true
                                   (@sigmaI (list exp) (fun l => sigma (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val ))))) [e]
                                            (@sigmaI nat (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val )))) fuel
                                                     (@sigmaI (state A) (fun st => sigma (fun sem => sigma (fun v1 => val ))) st
                                                              (@sigmaI (sem_env val) (fun sem => sigma (fun v1 => val )) {| sev := (nsAppend (alist_to_ns a) (sev env)); sec := sec env |}
                                                                       (@sigmaI val (fun v1 => val) uu uu)))))))
          as ididit.
        assert (ididit = ididit) by auto.
        rewrite Heqididit in H3.
        Check H0.
        specialize (H0 n a fuel true [e] st st' {| sev := nsAppend
                                                            (alist_to_ns a)
                                                            (sev env);
                                                   sec := sec env |}
                       uu uu res H1 H2 H3).
        apply H0.
        unfold eq_rect.
        dependent destruction H3.
        congruence.
    + congruence.
Qed.

Lemma evaluate_inc_fuel_res : forall (f : nat) (es : list exp) (st st' : state A)
                                (env : sem_env val) (res : result (list val) val),
    res <> Rerr (Rabort Rtimeout_error) ->
    evaluate es f st env = (st', res) ->
    evaluate es (S f) st env = (st', res).
Proof.
  intros.
  apply eval_or_match_inc_fuel_res; assumption.
Qed.

Lemma more_fuel_same_result : forall (n f: nat) (st st' : state A) (env : sem_env val) (res : result (list val) val) (es : list exp),
    res <> Rerr (Rabort Rtimeout_error) ->
    eval_or_match true es f st env uu uu = (st', res) ->
    eval_or_match true es f st env uu uu = eval_or_match true es (n+f) st env uu uu.
Proof.
  induction n.
  - intros. reflexivity.
  - intros.
    rewrite H0.
    apply eval_or_match_inc_fuel_res in H0; try assumption.
    rewrite <- H0.
    rewrite plus_Snm_nSm.
    apply IHn with st' res; try assumption.
Qed.

Theorem ELannot_does_nothing : forall (e : exp) (l : locs) (f : nat) (st : state A) (env : sem_env val),
    evaluate [ELannot e l] f st env = evaluate [e] f st env.
Proof.
  intros e l f st env.
  unfold evaluate.
  simp eval_or_match.
  congruence.
Qed.

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

Theorem eval_or_match_len_exp_len_val : forall (sel : bool) (es : if sel then list exp else list (pat * exp)) (f : nat) (st st' : state A) (env : sem_env val) (match_v err_v : val) (vs : list val),
  eval_or_match sel es f st env match_v err_v = (st', Rval vs) ->
  length vs = if sel then length vs else 1.
Proof.
  intros.
  funelim (eval_or_match sel es f st env match_v err_v); try reflexivity.
  - congruence.
  - simpl in *.
    break_if.
    + rewrite H1 in Heqcall.
      break_match; try congruence.
      * apply H with st'.
        assumption.
        assumption.
      * apply eval_or_match_sing in Heqcall.
        destruct Heqcall.
        rewrite H2. reflexivity.
    + rewrite H1 in Heqcall. congruence.
Qed.
Check Forall.

Definition noTimeout e f (st : state A) env st' :=
  eval_or_match true [e] f st env uu uu <> (st', Rerr (Rabort Rtimeout_error)).

Theorem exp_no_div_sub_exp_no_div : forall (es : list exp ) (f : nat) (st st' : state A) (env : sem_env val)
                                      (res : result (list val) val),
    res <> Rerr (Rabort Rtimeout_error) ->
    eval_or_match true es f st env uu uu = (st', res) ->
    Forall (fun e => noTimeout e f st env st') es.
Proof.
  intros.
  funelim (eval_or_match true es f st env uu uu); try solve [constructor]; try (solve [constructor; try (unfold noTimeout; destruct res; congruence); try constructor]).
  - clear Heqcall.
    simpl in *.
    rewrite eval_or_match_cons in *.
    rewrite eval_or_match_cons in *.
    simp eval_or_match in *.
    constructor.
    unfold noTimeout.
    destruct (eval_or_match true [e] fuel st env uu uu).
    destruct r.
    congruence.
    destruct e1; congruence.
    destruct (eval_or_match true (e0::l) fuel st' env uu uu) eqn:eval1.
    Check H0.












Abort.

(* Theorem state_never_changes : forall (sel : bool) (es : if sel then list exp else list (pat * exp)) *)
(*                                 (f : nat) (st st' : state A) (env : sem_env val) (match_v err_v : val) (res : result (list val) val), *)
(*     eval_or_match sel es f st env match_v err_v = (st', res) -> *)
(*     st = st'. *)
(* Proof. *)
(*   intros. *)
(*   funelim (eval_or_match sel es f st env match_v err_v); simp eval_or_match in *; simpl in *. *)
(*   - inv H; congruence. *)
(*   - break_if; try congruence. *)
(*     break_match. *)
(*     apply H with r. *)
(*     break_match. *)
(*     break_match; *)
(*       inv H0; congruence. *)
(*     inv H0; congruence. *)
(*   - break_match; inv H; congruence. *)
(*   - inv H; congruence. *)
(*   - inv H; congruence. *)
(*   - unfold eq_rect in *; simpl in *. *)
(*     break_let. *)
(*     break_match. *)
(*     break_if. *)
(*     break_match. *)
(*     break_let. *)

(*     pose proof (@eq_refl _ (@sigmaI Type (fun x => sigma (fun b : bool => sigma (fun l : if b then list exp else list (pat * exp) => sigma (fun n => sigma (fun st : state x => sigma (fun sem => sigma (fun v1 => val ))))))) A *)
(*                           (@sigmaI bool (fun b : bool => sigma (fun l : if b then list exp else list (pat * exp) => sigma (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val )))))) true *)
(*                                    (@sigmaI (list exp) (fun l => sigma (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val ))))) [e0] *)
(*                                             (@sigmaI nat (fun n => sigma (fun st => sigma (fun sem => sigma (fun v1 => val )))) n *)
(*                                                      (@sigmaI (state A) (fun st => sigma (fun sem => sigma (fun v1 => val ))) s *)
(*                                                               (@sigmaI (sem_env val) (fun sem => sigma (fun v1 => val )) s0 *)
(*                                                                        (@sigmaI val (fun v1 => val) uu uu)))))))) as SigEq. *)
(*     specialize (H0 s res l e p s0 e0 true [e0] n s st' s0 uu uu res H1 SigEq). *)
(*     dependent destruction SigEq. *)
(*     rewrite <- Heqp in H. *)
(*     specialize (H s (Rval l)). *)
(*     apply H in Heqp. *)
(*     apply H0 in Heqcall. *)
(*     subst. reflexivity. *)
(*     apply (H st' (Rval l)). *)
(*     inv H1. reflexivity. *)
(*     apply (H st' (Rval l)). *)
(*     inv H1. reflexivity. *)
(*     apply (H st' (Rerr e)). *)
(*     inv H1. *)
(*     reflexivity. *)
(*   - break_let. *)
(*     break_match. *)
(*     break_match. *)
(*     apply (H st' (Rval l)). *)
(*     inv H1. reflexivity. *)
(*     Check H0. *)
(*     specialize (H0 ) *)






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
  intros.
  unfold evaluate in *.
  apply eval_or_match_inc_fuel_res in H4; try congruence.
  apply eval_or_match_inc_fuel_res in H4; try congruence.
  apply eval_or_match_inc_fuel_res in H4; try congruence.
  apply eval_or_match_inc_fuel_res in H4; try congruence.
  simp eval_or_match in *; simpl in *.
  rewrite eval_or_match_cons in H4; simpl in *.
  apply eval_or_match_inc_fuel_res in H1; try congruence.
  apply eval_or_match_inc_fuel_res in H1; try congruence.
  apply eval_or_match_inc_fuel_res in H1; try congruence.
  rewrite H1 in H4.
  simp eval_or_match in *; simpl in *.
  simp eval_or_match in *; simpl in *.
  apply eval_or_match_inc_fuel_res in H0; try congruence.
  apply eval_or_match_inc_fuel_res in H0; try congruence.
  rewrite H0 in H4.
  simp eval_or_match in *; simpl in *.
  Opaque ident_string_dec.
  simp eval_or_match in *; simpl in *.
  simp eval_or_match in *; simpl in *.
  Transparent ident_string_dec.
  Opaque build_rec_env.
  simp eval_or_match in *; simpl in *.
  Opaque ident_string_dec.
  simp eval_or_match in *; simpl in *.
  revert H H0 H1 H3 H4. revert n env m_exp n_exp.
  induction H2.
  - intros. Transparent ident_string_dec. Opaque stamp_eq_dec. simpl in *.
    destruct (stamp_eq_dec (TypeStamp "O" 0) (TypeStamp "O" t)).
    + simp eval_or_match in H4; simpl in H4.
      inv H4.
      apply H3.
    + destruct (stamp_eq_dec (TypeStamp "S" 0) (TypeStamp "O" t)); inv H4.
  - intros. simpl in H4.
    destruct (stamp_eq_dec (TypeStamp "O" 0) (TypeStamp "S" t)); try congruence.
    destruct (stamp_eq_dec (TypeStamp "S" 0) (TypeStamp "S" t)); try congruence.
    simp eval_or_match in H4; simpl in H4.
    simp eval_or_match in H4; simpl in H4.
    simp eval_or_match in H4; simpl in H4.
    simp eval_or_match in H4; simpl in H4.
    simp eval_or_match in H4; simpl in H4.
    simp eval_or_match in H4; simpl in H4.
    Transparent build_rec_env. simpl in H4.
    simp eval_or_match in H4; simpl in H4.
    simp eval_or_match in H4; simpl in H4.
    simp eval_or_match in H4; simpl in H4.
    Transparent build_rec_env. simpl in *.
    simp eval_or_match in H4; simpl in H4.
    simp eval_or_match in H4; simpl in IHnat_rel_cake_nat.
    destruct prev; try congruence.
    break_match.
    break_inner_match.
    break_inner_match.
    break_inner_match.
    break_inner_match.
    inv H4.
    simp eval_or_match in *; simpl in *.
    inv Heqp.
    Search "plus".
    rewrite <- plus_Sn_m.
    rewrite plus_Snm_nSm.
    eapply IHnat_rel_cake_nat.
    apply H.

  (* I'm not sure which one is easier *)
  intros.
  revert H H0 H1 H3 H4. revert env m_n_val n_val n_exp m_exp f n.
  induction H2; unfold evaluate in *.
  - intros.
    apply eval_or_match_inc_fuel_res in H4; try congruence.
    apply eval_or_match_inc_fuel_res in H4; try congruence.
    apply eval_or_match_inc_fuel_res in H4; try congruence.
    simp eval_or_match in H4.
    simpl in*.
    simp eval_or_match in H4.
    apply eval_or_match_inc_fuel_res in H1; try congruence.
    apply eval_or_match_inc_fuel_res in H1; try congruence.
    rewrite H1 in H4.
    simp eval_or_match in H4.
    simpl in *.
    simp eval_or_match in H4.
    apply eval_or_match_inc_fuel_res in H0; try congruence.
    rewrite H0 in H4.
    Opaque stamp_eq_dec.
    simp eval_or_match in H4; simpl in *.
    simp eval_or_match in H4; simpl in *.
    simp eval_or_match in H4; simpl in  *.
    simp eval_or_match in H4; simpl in  *.
    destruct (stamp_eq_dec (TypeStamp "O" 0) (TypeStamp "O" t)).
    + simp eval_or_match in H4; simpl in  *.
      inv H4. assumption.
    + destruct (stamp_eq_dec (TypeStamp "S" 0) (TypeStamp "O" t));
        simp eval_or_match in H4; simpl in *; inv H4.
  - intros.
    simp eval_or_match in *; simpl in  *.
    destruct (op_eq_dec); try congruence.
    simpl in *.
    simp eval_or_match in H4.
    simpl in *.
    simp eval_or_match in H4.
    destruct NoDuplicates_dec; try congruence.
    simpl in *.
    break_if; try congruence.
    simp eval_or_match in H4.
    simpl in *.
    inv H4.
    assumption.
  - intros.
    apply eval_or_match_inc_fuel_res in H4; try congruence.
    apply eval_or_match_inc_fuel_res in H4; try congruence.
    apply eval_or_match_inc_fuel_res in H4; try congruence.
    simp eval_or_match in H4; simpl in *.
    simp eval_or_match in H4; simpl in *.
    apply eval_or_match_inc_fuel_res in H1; try congruence.
    apply eval_or_match_inc_fuel_res in H1; try congruence.
    rewrite H1 in H4.
    simp eval_or_match in H4; simpl in *.
    simp eval_or_match in H4; simpl in *.
    apply eval_or_match_inc_fuel_res in H0; try congruence.
    rewrite H0 in H4.
    simp eval_or_match in H4; simpl in *.
    break_if; try congruence.
    simp eval_or_match in H4; simpl in *.
    simp eval_or_match in H4; simpl in *.
    simp eval_or_match in H4.
    Opaque NoDuplicates_dec.
    destruct NoDuplicates_dec.
    simpl in H4.
    break_if. break_if; try congruence.
    clear Heqs.
    simp eval_or_match in H4; simpl in *.
    simp eval_or_match in H4; simpl in *.
    simp eval_or_match in H4; simpl in *.
    simp eval_or_match in H4; simpl in *.
    simp eval_or_match in H4; simpl in *.
    simp eval_or_match in H4; simpl in *.
    assert (SECCLEAN : forall (V : Type) (e : sem_env V) x, sec (update_sev e x) = sec e) by reflexivity.
    simp eval_or_match in H4; simpl in *.
    break_if; try congruence.
    break_if; try congruence.
    simp eval_or_match in H4; simpl in *.
    simp eval_or_match in H4; simpl in *.
    simp eval_or_match in H4. rewrite SECCLEAN in H4.
)
