From TLC Require Import LibLogic.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Namespace.

Lemma lookup_cover : forall (N V: Type) (n : N) (ns ns' : alist N V) (v : V),
    lookup n ns = Some v ->
    lookup n (ns ++ ns') = lookup n ns.
Proof.
  intros N V n ns ns' v.
  generalize dependent ns'.
  induction ns; intros ns' H.
  - inversion H.
  - destruct a. inversion H; subst; clear H.
    assert ({n = n0} + {n <> n0}) by apply (classicT (n = n0)).
    destruct H; simpl.
    + rewrite e. rewrite 2 If_l; reflexivity.
    + rewrite 2 If_r in *; try (assumption). apply IHns. assumption.
Qed.

Lemma lookup_drop : forall (N V: Type) (id : N) (ns ns' : alist N V),
    lookup id ns = None ->
    lookup id (ns ++ ns') = lookup id ns'.
Proof.
  intros N V id ns.
  induction ns; intros ns' H.
  - reflexivity.
  - destruct a; simpl in *.
    assert ({id = n} + {id <> n}) as loem by apply (classicT (id = n)).
    destruct loem.
    + rewrite <- e in *. rewrite If_l in H; try (reflexivity). inversion H.
    + rewrite If_r in *; try (assumption). apply IHns. assumption.
Qed.

Lemma lookup_none : forall (N V: Type) (n : N) (ns ns' : alist N V),
    lookup n ns = None ->
    lookup n (ns ++ ns') = lookup n ns'.
Proof.
  intros N V n ns ns'.
  generalize dependent ns'.
  induction ns; intros ns'.
  - reflexivity.
  - destruct a.
    assert ({n = n0} + {n <> n0}) as loem by apply (classicT (n = n0)).
    destruct loem; simpl.
    + rewrite e. rewrite 2 If_l; try (reflexivity). intro H. inversion H.
    + rewrite 2 If_r; try (assumption). apply IHns.
Qed.

Lemma lookup_same : forall (N V: Type) (n : N) (ns : alist N V),
    lookup n (ns ++ ns) = lookup n ns.
Proof.
  intros N V n ns.
  destruct (lookup n ns) eqn:H; rewrite <- H.
  - apply lookup_cover with v; assumption.
  - apply lookup_none; assumption.
Qed.

Lemma get_modded_namespace_append : forall (M N V : Type) (ns ns' : namespace M N V) (x : M),
    get_modded_namespace x (ns ++ ns') = (get_modded_namespace x ns) ++ (get_modded_namespace x ns').
Proof.
  intros M N V.
  induction ns; intros ns' x.
  - reflexivity.
  - destruct a. destruct i.
    + apply IHns.
    + simpl. assert ({x = m} + {x <> m}) as loem by (apply (classicT (x = m))).
      destruct loem.
      * rewrite <- e. rewrite 2 If_l; try (reflexivity). unfold app. simpl. rewrite IHns. reflexivity.
      * rewrite 2 If_r; try (assumption). apply IHns.
Qed.

Lemma nsLookup_empty : forall (M N V: Type) (id : ident M N), nsLookup id ([] : namespace M N V) = None.
Proof.
  reflexivity.
Qed.

Lemma nsLookup_cover : forall (M N V: Type) (id : ident M N) (ns ns' : namespace M N V) (v : V),
    nsLookup id ns = Some v ->
    nsLookup id (ns ++ ns') = nsLookup id ns.
Proof.
  intros. unfold nsLookup in *. apply lookup_cover with v. assumption.
Qed.

Lemma nsLookup_drop : forall (M N V: Type) (id : ident M N) (ns ns' : namespace M N V),
    nsLookup id ns = None ->
    nsLookup id (ns ++ ns') = nsLookup id ns'.
Proof.
  intros M N V id ns ns' H.
  unfold nsLookup in *. apply lookup_drop. assumption.
Qed.

Lemma nsLookup_same : forall (M N V: Type) (id : ident M N) (ns : namespace M N V),
    nsLookup id (ns ++ ns) = nsLookup id ns.
Proof.
  intros M N V id ns.
  unfold nsLookup in *. apply lookup_same.
Qed.
