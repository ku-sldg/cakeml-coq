Require Import Coq.Program.Wf.
Require Import Coq.Arith.Arith.

(* Definition lexicographic_ordering (ab1 ab2 : nat * nat) : Prop := *)
(*   match ab1, ab2 with *)
(*   | (a1, b1), (a2, b2) => *)
(*       (a1 < a2) \/ ((a1 = a2) /\ (b1 < b2)) *)
(*   end. *)

Inductive lexicographic_ordering : nat * nat -> nat * nat -> Prop :=
| first_eq : forall (a b1 b2 : nat), b1 < b2 -> lexicographic_ordering (a, b1) (a, b2)
| first_less : forall (a1 a2 b1 b2 : nat), a1 < a2 -> lexicographic_ordering (a1, b1) (a2, b2).


(* this is defined in stdlib, but unfortunately it is opaque *)
Lemma lt_wf_ind :
  forall n (P:nat -> Prop), (forall n, (forall m, m < n -> P m) -> P n) -> P n.
Proof. intro p; intros; elim (lt_wf p); auto with arith. Defined.

(* this is defined in stdlib, but unfortunately it is opaque too *)
Lemma lt_wf_double_ind :
  forall P:nat -> nat -> Prop,
    (forall n m,
      (forall p (q:nat), p < n -> P p q) ->
      (forall p, p < m -> P n p) -> P n m) -> forall n m, P n m.
Proof.
  intros P Hrec p. pattern p. apply lt_wf_ind.
  intros n H q. pattern q. apply lt_wf_ind. auto.
Defined.

Lemma lexicographic_ordering_wf : well_founded lexicographic_ordering.
Proof.
  intros (a, b); pattern a, b; apply lt_wf_double_ind.
  intros m n H1 H2.
  constructor. intros (m', n') G.
  inversion G.
  - now apply H2.
  - now apply H1.
Defined.
