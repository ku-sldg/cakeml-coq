Require Import Ascii.
Require Import Strings.String.
Require Import Lists.List.
Import ListNotations.

From TLC Require LibList.

Require NoBasis.
Require Import FFI.
Require Import Namespace.
Require Import CakeAST.
Require Import SemanticsAux.
Require Import RelationalBigStep.

Axiom alreadyTypeChecked : forall x, TypeCheck x.


Definition init_env : sem_env val := empty_sem_env.
Definition init_store := empty_store val.

Parameter A : Type.
Parameter init_ffi_st : ffi_state A.
Definition init_state := Build_state 0 init_store init_ffi_st 0 0.

Ltac inv H := inversion H; subst; clear H.

Ltac TCDone := apply alreadyTypeChecked.

Ltac bigR := rewrite LibLogic.If_r; try(discriminate); try (reflexivity).
Ltac bigL := rewrite LibLogic.If_l; try(reflexivity).

Ltac elim_nsLookup := unfold nsLookup; simpl;
  match goal with
    | [ |- (if LibLogic.classicT (Short ?x = Short ?x) then _ else _)  = Some _ ] => bigL
    | [ |- (if LibLogic.classicT (Long ?m ?x = Long ?m ?x) then _ else _)  = Some _ ] => bigL
    | [ |- (if LibLogic.classicT (?x = ?x) then _ else _)  = Some _ ] => bigL
    | [ |- (if LibLogic.classicT (?x = ?y) then _ else _)  = None ]   => bigR; elim_nsLookup
    | [ |- (if LibLogic.classicT (?x = ?y) then _ else _)  = Some _ ] => bigR; elim_nsLookup
  end.

Ltac elim_con_build :=
  match goal with
    | [ |- con_build _ None _ ] => econstructor
    | [ |- con_build _ _ None ] => econstructor
    | [ |- con_build _ (Some _) _ ] => econstructor; elim_nsLookup
    | [ |- con_build _ _ (Some _) ] => econstructor; elim_nsLookup
  end.

Ltac elim_opapp :=
  match goal with
  | [|- opapp (Closure _ _ _) _ _ _] => econstructor
  | [|- opapp (Recclosure _ _ _) _ _ _] => econstructor;
                                         [ TCDone
                                         | reflexivity
                                         | elim_nsLookup ]
  end.

Ltac elim_pmatchR :=
  match goal with
  | [|- pmatchR _ _ Pany _ (Match _)] => econstructor
  | [|- pmatchR _ _ (Pvar ?x) ?v (Match _) ] => econstructor
  | [|- pmatchR _ _ (Plit ?l) (Litv ?l) (Match _)] => econstructor
  | [|- pmatchR _ _ (Plit ?l1) (Litv ?l2) No_match] => econstructor;
                                                     [ TCDone
                                                     | discriminate ]
  | [|- pmatchR _ _ (Pcon None _)     (Conv None _) _] => econstructor; elim_pmatchRList
  | [|- pmatchR _ _ (Pcon (Some _) _) (Conv (Some _) _) No_match] => econstructor;
                                                                   [ elim_nsLookup
                                                                   | TCDone
                                                                   | discriminate ]
  | [|- pmatchR _ _ (Pcon (Some _) _) (Conv (Some _) _) _] => econstructor;
                                                            [ elim_nsLookup
                                                            | elim_pmatchRList ]
  | [|- pmatchR _ _ (Pref _) (Loc _) _] => econstructor;
                                         [ econstructor
                                         | elim_pmatchR ]

  | [|- pmatchR _ _ (Ptannot _ _) _ _] => econstructor; elim_pmatchR
  end

with elim_pmatchRList :=
    match goal with
    | [ |- pmatchListR _ _ [] [] (Match _)] => econstructor
    | [ |- pmatchListR _ _ _ _ (Match _)]    => econstructor;
                                              [ elim_pmatchR
                                              | elim_pmatchRList ]
    | [ |- pmatchListR _ _ _ _ No_match]     => econstructor;
                                              [ elim_pmatchR
                                              | elim_pmatchRList ]
    end.

Ltac elim_matR :=
  match goal with
    | [ |- matR _ _ _ [] None ] => econstructor
    | [ |- matR _ _ _ _ None ] => econstructor;
                                 [ TCDone
                                 | elim_pmatchR
                                 | elim_matR ]
    | [ |- matR _ _ _ _ (Some _) ] => econstructor;
                                 [ TCDone
                                 | left; split;
                                   [ elim_pmatchR
                                   | reflexivity] ]
    | [ |- matR _ _ _ _ (Some _) ] => econstructor;
                                 [ TCDone
                                 | right; elim_matR ]
  end.


Ltac elim_expR :=
  match goal with
    | [ |- expR _ _ (ELit _) _ ] => econstructor
    | [ |- expR _ _ (ECon _ _) _ ] => econstructor;
                                    [ TCDone
                                    | elim_expListRevR
                                    | elim_con_build ]
    | [ |- expR _ _ (EVar _) _ ] => econstructor; elim_nsLookup
    | [ |- expR _ _ (EFun _ _) _ ] => econstructor
    | [ |- expR _ _ (EApp Opapp _) _ ] => econstructor;
                                        [ elim_expListRevR
                                        | elim_opapp
                                        | reflexivity
                                        | elim_expR ]
    | [ |- expR _ _ (EApp _ _) _ ] => econstructor;
                                    [ discriminate
                                    | elim_expListRevR
                                    | idtac "need to do appR"
                                    | reflexivity ]
    | [ |- expR _ _ (ELog _ _ _) _ ] => econstructor;
                                  [ elim_expR
                                  | simpl; reflexivity ]
    | [ |- expR _ _ (ELog _ _ _) _ ] => econstructor;
                                  [ elim_expR
                                  | simpl; reflexivity
                                  | elim_expR]
    | [ |- expR _ _ (EIf _ _ _) _ ] => econstructor;
                                     idtac "implement IF"
                                  (* [ intro H; simpl; try (inv H); elim_expR *)
                                  (* | intro H; simpl; try (inv H); elim_expR ] *)
    | [ |- expR _ _ (EMat _ _) _ ] => econstructor;
                                    [ elim_expR
                                    | elim_matR
                                    | reflexivity
                                    | elim_expR ]
    | [ |- expR _ _ (EMat _ _) _ ] => econstructor;
                                    [ elim_expR
                                    | elim_matR
                                    | reflexivity
                                    | elim_expR ]
    | [ |- expR _ _ (ELet _ _ _) _ ] => econstructor;
                                      [ elim_expR
                                      | reflexivity
                                      | elim_expR ]
    | [ |- expR _ _ (ELetrec _ _) _ ] => econstructor;
                                       [ reflexivity
                                       | elim_expR ]
    | [ |- expR _ _ (ETannot _ _) _ ] => econstructor;
                                       elim_expR
    | [ |- expR _ _ (ELannot _ _) _ ] => econstructor;
                                       elim_expR
    | [ |- expR _ _ ?x _ ] => idtac x
  end
with elim_expListRevR :=
    match goal with
    | [ |- expListRevR _ _ [] _ ] => econstructor
    | [ |- expListRevR _ _ _ _ ] => econstructor;
                                  [ elim_expListRevR
                                  | elim_expR]
    end.

Ltac decReliminateDtype :=
  econstructor;
  [ TCDone
  | econstructor
  | econstructor ].

Ltac decReliminateDlet := econstructor;
                          [ TCDone
                          | elim_expR
                          | elim_pmatchR
                          | econstructor ].


Ltac decReliminateDletrec :=
  econstructor;
  [ apply alreadyTypeChecked
  | econstructor ].

Ltac decReliminateDexn :=
  econstructor;
  [ econstructor
  | econstructor ].

Ltac decReliminate := (decReliminateDexn + decReliminateDlet + decReliminateDletrec + decReliminateDtype).
(* Ltac decReliminate := *)
(*   match goal with *)
(*   | [ |- decR _ _ (Dlet _ _ _) _ ] => econstructor; *)
(*                                     [ TCDone *)
(*                                     | elim_expR *)
(*                                     | elim_pmatchR *)
(*                                     | econstructor ] *)
(*   | [ |- decR _ _ (Dletrec _ _) _ ] => econstructor; *)
(*                                      [ TCDone *)
(*                                      | econstructor ] *)
(*   | [ |- decR _ _ (Dtype _ _) _ ] => econstructor; *)
(*                                    [ TCDone *)
(*                                    | econstructor *)
(*                                    | econstructor ] *)
(*   | [ |- decR _ _ (Dexn _ _) _ ] => econstructor; *)
(*                                   [ econstructor *)
(*                                   | econstructor ] *)
(*   | [ |- decR _ _ _ _ ] => idtac "decR unfinished" *)
(*   end. *)


  Ltac cleanupEnv := unfold update_sev; simpl;
                     unfold state_update_next_exn_stamp; simpl;
                     unfold state_update_next_type_stamp; simpl;
                     unfold next_type_stamp; simpl;
                     unfold init_state; simpl;
                     unfold extend_dec_env; simpl;
                     unfold build_rec_env; simpl;
                     unfold nsBind; simpl.

Lemma st_no_basis : {st : state A |
                         exists env, decListR init_state init_env NoBasis.prog (st, Rval env)}.
Proof.
  econstructor.
  econstructor.

  econstructor.
  decReliminate.

  econstructor.
  decReliminate.

  econstructor.
  decReliminate.

  econstructor.
  decReliminate.

  econstructor.
  decReliminate.

  econstructor.
  decReliminate.

  econstructor.
  decReliminate.

  econstructor.
  decReliminate.

  econstructor.
  decReliminate.

  econstructor.
  decReliminate.

  cleanupEnv.
  econstructor.
  decReliminate.

  econstructor.
Defined.

Lemma env_no_basis : {env : sem_env val |
                         exists st, decListR init_state init_env NoBasis.prog (st, Rval env)}.
Proof.
  econstructor.
  econstructor.

  econstructor.
  decReliminate.

  econstructor.
  decReliminate.

  econstructor.
  decReliminate.

  econstructor.
  decReliminate.

  econstructor.
  decReliminate.

  econstructor.
  decReliminate.

  econstructor.
  decReliminate.

  econstructor.
  decReliminate.

  econstructor.
  decReliminate.

  econstructor.
  decReliminate.

  econstructor.
  decReliminate.

  econstructor.
Defined.

Definition curr_st := proj1_sig st_no_basis.
Definition curr_env := proj1_sig env_no_basis.

Inductive NatCakeRel : nat -> val -> Prop :=
| O_rel : forall (type_num : nat), NatCakeRel O (Conv (Some (TypeStamp "O" type_num)) [])
| S_rel  : forall (n' : nat) (type_num : nat) (conv : val),
    NatCakeRel n' (conv) -> NatCakeRel (S n') (Conv (Some (TypeStamp "S" type_num)) [conv]).

Fixpoint generateNatVal (n : nat) : nat -> val := match n with
                                             | O => fun x => Conv (Some (TypeStamp "O" x)) []
                                             | S n' => fun x => Conv (Some (TypeStamp "S" x)) [generateNatVal n' x]
                                             end.

Fixpoint generateNatTerm (n : nat) : nat -> exp := match n with
                                              | O => fun x => ECon (Some (Short "O")) []
                                              | S n' => fun x => ECon (Some (Short "S")) [generateNatTerm n' x]
                                              end.

Theorem generateRel : forall (n ts : nat), NatCakeRel n (generateNatVal n ts).
Proof.
  intro n. induction n; intro ts.
  simpl. constructor.
  simpl. constructor.
  apply IHn.
Qed.

Theorem generateExpRel : forall (n ts : nat) (nv : val),
    expR curr_st curr_env (generateNatTerm n ts) (curr_st, Rval nv) -> NatCakeRel n nv.
Proof.
  (* split; generalize dependent nv; generalize dependent ts. *)
  - induction n; intros ts nv H; simpl in *.
    + inv H. simpl in *.
      inv H5. inv H6. unfold nsLookup in H0. simpl in H0. rewrite LibLogic.If_r in H0.
      rewrite LibLogic.If_r in H0. rewrite LibLogic.If_l in H0. inv H0. constructor.
      reflexivity. discriminate. discriminate.
    + inv H. simpl in *.
      inv H5. inv H6. unfold nsLookup in H0. simpl in H0. rewrite LibLogic.If_r in H0.
      rewrite LibLogic.If_l in H0. inv H0. inv H2. constructor. apply IHn with ts.
      assumption. reflexivity. discriminate.
Qed.

Theorem cakePlusIsPlus : forall (n m r : nat) (ne me : exp) (nv mv rv : val),
    expR curr_st curr_env ne (curr_st, Rval nv) ->
    expR curr_st curr_env me (curr_st, Rval mv) ->
    NatCakeRel n nv ->
    NatCakeRel m mv ->
    r = n + m ->
    expR (proj1_sig st_no_basis) (proj1_sig env_no_basis)
         (EApp Opapp [(EApp Opapp [(EVar (Short "plus")); ne]); me])
         ((proj1_sig st_no_basis), Rval rv) ->
    NatCakeRel r rv.
Proof.
  intros n m r ne me nv mv rv Hnev Hmev Hreln Hrelm Hsum HexpR.
  induction n;
    rewrite Hsum. simpl.
  - inv HexpR.
    inv H1.
    inv H3.
