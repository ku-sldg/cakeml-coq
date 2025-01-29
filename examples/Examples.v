Inductive Option : Set :=
| Fail : Option
| Ok : bool -> Option.

Definition get : forall x:Option, x <> Fail -> bool.
refine
    (fun x:Option =>
      match x return x <> Fail -> bool with
      | Fail => _
      | Ok b => fun _ => b
      end).
congruence.
Defined.

(* Start of Dominique's Solution *)
Require Import Wf.
Require Import List.
Import ListNotations.

Fixpoint In_t {A : Type} (x : A) (l : list A) : Type :=
  match l with
  | [] => False
  | h::t => (x = h) + (In_t x t)
  end.

Set Implicit Arguments.

Unset Elimination Schemes.

Inductive arb : Type :=
| A : nat -> arb
| B : nat -> list (nat * arb) -> arb.

Set Elimination Schemes.

Section arb_rect'.
  Variables (P : arb -> Type)
            (H1 : forall (n : nat), P (A n))
            (H2 : forall (n : nat) (l : list (nat * arb)), (forall p, In_t p l -> P (snd p)) -> P (B n l)).

  Fixpoint arb_rect a : P a.
  Proof.
    destruct a.
    - apply H1.
    - apply H2.
      revert l.
      refine (fix loop al := _).
      destruct al.
      + intros p H.
        inversion H.
      + intros p0 H.
        destruct H.
        * destruct p.
          rewrite e.
          simpl.
          apply arb_rect.
        * apply loop with al.
          assumption.
  Qed.

End arb_rect'.

Section arb_rect.

  Let R (x y : arb) :=
    match y with
      | A _ => False
      | B _ l => exists n, In (n,x) l
    end.

  Fixpoint Rwf x : Acc R x.
  Proof.
    destruct x as [ n | n l ].
    + constructor. intros. inversion H.
    (* + constructor. intros x H. destruct H as [m Hm]. apply Rwf. *)
    + constructor; intros x (m & Hm).
      revert l Hm. refine (fix loop l := _).
      destruct l as [ | (k,y) l ].
      * intros [].
      * intros [ E | H ].
        - generalize (Rwf y).
          inversion E; trivial.
        - apply (loop l), H.
  Defined.

  Variables (P : arb -> Type)
            (H1 : forall (n : nat), P (A n))
            (H2 : forall (n : nat) (l : list (nat * arb)), (forall p, In p l -> P (snd p)) -> P (B n l)).

  Definition arb_rect : forall a, P a.
  Proof.
    Check Fix.
    apply Fix with (1 := Rwf).
    intros [ n | n l ] H.
    + apply H1.
    + apply H2.
      intros (m,x) Hmx.
      apply H; exists m; trivial.
  Defined.

  Hypothesis H2_ext : forall n l f g, (forall p Hp, f p Hp = g p Hp) -> H2 n l f = H2 n l g.

  Fact arb_rect_fix_1 n : arb_rect (A n) = H1 n.
  Proof.
    unfold arb_rect at 1.
    unfold Fix.
    now rewrite <- Fix_F_eq.
  Qed.

  Fact arb_rect_fix_2 n l : arb_rect (B n l) = H2 n l (fun p _ => arb_rect (snd p)).
  Proof.
    unfold arb_rect at 1.
    unfold Fix.
    rewrite <- Fix_F_eq.
    apply H2_ext.
    intros (m,b) H.
    Search Fix_F.
    apply Fix_F_inv.
    + red; apply Rwf.
    + intros []; auto.
      intros f g Hfg; apply H2_ext.
      intros [] ?; apply Hfg.
  Qed.

End arb_rect.

Print arb_rect.

Definition arb_rec (P : arb -> Set) := arb_rect P.
Definition arb_ind (P : arb -> Prop) := arb_rect P.

Section list_In_map.

  Variable (X Y : Type).

  Fixpoint list_In_map l : (forall x : X, In x l -> Y) -> list Y.
  Proof.
    refine (match l with
      | []   => fun _ => []
      | x::l => fun f => f x _ :: list_In_map l _
    end).
    + left. trivial.
    + intros x' ?. apply (f x'). right. trivial.
  Defined.

  Fact list_In_map_ext l f g :
         (forall x Hx, f x Hx = g x Hx)
      -> list_In_map l f = list_In_map l g.
  Proof.
    revert f g; induction l as [ | x l IHl ]; simpl; f_equal; auto.
    intros f g Hfg; rewrite Hfg; f_equal.
    apply IHl.
    intros; apply Hfg.
  Qed.

  Variable (f : X -> Y).

  Fact list_In_map_map l : list_In_map l (fun x _ => f x) = map f l.
  Proof. induction l; simpl; f_equal; auto. Qed.

End list_In_map.

Section arb_recursion.

  Variables (T : Type)
            (f1 : nat -> T)
            (f2 : nat -> list (nat*T) -> T).

  Definition arb_recursion : arb -> T.
  Proof.
    apply arb_rect.
    + apply f1.
    + intros n l Hl.
      apply (f2 n).
      apply (list_In_map l).
      intros p Hp; split.
      * apply (fst p).
      * apply (Hl _ Hp).
  Defined.

  Fact arb_recursion_fix_1 n : arb_recursion (A n) = f1 n.
  Proof.
    unfold arb_recursion.
    now rewrite arb_rect_fix_1.
  Qed.

  Fact arb_recursion_fix_2 n l : arb_recursion (B n l) = f2 n (map (fun
'(i,a) => (i,arb_recursion a)) l).
  Proof.
    unfold arb_recursion.
    rewrite arb_rect_fix_2.
    + f_equal.
      rewrite list_In_map_map.
      apply map_ext.
      intros []; simpl; auto.
    + intros; f_equal; apply list_In_map_ext.
      intros; f_equal; auto.
  Qed.

End arb_recursion.

Definition flatten : arb -> list nat.
Proof.
  apply arb_recursion.
  + intros n . exact [n].
  + intros n l.
    destruct l.
    exact [n].
    destruct p.
    exact (n::n0::l0 ++ flat_map (fun c => snd c) l).
Defined.

Print flatten.

Definition flattener : list arb -> list nat := fun xs => fold_right (@app nat) [] (map flatten xs).


Eval compute in flatten (B 3 [(4, A 5)]).
Eval compute in flattener [B 3 [(4, A 5)]; A 6].

Fact flatten_fix_1 n : flatten (A n) = [n].
Proof. apply arb_recursion_fix_1. Qed.

Fact flatten_fix_2 n l : flatten (B n l) = n::flat_map (fun p => flatten
(snd p)) l.
Proof.
  unfold flatten at 1.
  rewrite arb_recursion_fix_2; f_equal.
  rewrite !flat_map_concat_map, map_map; f_equal.
  apply map_ext; intros []; auto.
Qed.

(* End of Dominique's Example *)


(* Inductive tree := T (A: list tree). *)
(* Implicit Type s t: tree. *)

(* Definition dst s t := let (A) := t in In s A. *)

(* Fixpoint tree_Acc t: Acc dst t. *)
(* Proof. *)
(*  destruct t as [A]. *)
(*  constructor. *)
(*  induction A as [| t A IH]; cbn. *)
(*  - intros t []. *)
(*  - intros s [[]|H]. *)
(*    + apply tree_Acc. *)
(*    + apply IH, H. *)
(* Defined. *)

Require Import Coq.Program.Wf.
Require Import Coq.Arith.Arith.

(* Ackermanns function example from StackOverflow *)

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
(* END of Ackermanns example *)

(* Tree example: doesn't actually show my problem *)
Unset Implicit Arguments.
Require Import List.
Import ListNotations.
Require Import Coq.Program.Wf.
Require Import Omega.

Inductive Forall' (A : Type) (P' : A -> Type) : list A -> Type :=
| Forall_nil' : Forall' A P' []
| Forall_cons' : forall (x : A) (l : list A), P' x -> Forall' A P' l -> Forall' A P' (x :: l).

Unset Elimination Schemes.

Inductive tree : Type :=
| Node : nat -> list tree -> tree.

Fixpoint tree_rect (P : tree -> Type)
         (H1 : forall (n : nat) (l : list tree), Forall' tree P l -> P (Node n l))
         (t : tree) : P t :=
  match t return (P t) with
  | Node n l => let fix loop (l : list tree) :=
                 match l with
                 | [] => Forall_nil' tree P
                 | t'::l' => Forall_cons' tree P t' l' (tree_rect P H1 t') (loop l')
                 end
             in
             H1 n l (loop l)
  end.

Definition tree_rec (P : tree -> Set) := tree_rect P.
Definition tree_ind (P : tree -> Prop) := tree_rect P.
Set Elimination Schemes.

Fixpoint size_tree (t : tree) : nat :=
  let fix size_tree_list (ts : list tree) : nat :=
      match ts with
      | [] => 0
      | t'::ts' => size_tree t' + size_tree_list ts'
      end
  in
  match t with
  | Node n l => 1 + size_tree_list l
  end.

Fixpoint size_tree_list (ts : list tree) : nat :=
  match ts with
  | [] => 0
  | t::ts' => size_tree t + size_tree_list ts'
  end.

Require Import Coq.Program.Wf.
Require Import Omega.

Program Fixpoint flatten_trees (ts : list tree) {measure (size_tree_list ts)}: list nat :=
  match ts with
  | [] => []
  | (Node n l)::ts' => n :: flatten_trees l ++ flatten_trees ts'
  end.
Obligation 1.
simpl.
fold size_tree_list.
omega.
Qed.
Obligation 2.
simpl.
fold size_tree_list.
omega.
Qed.

Fixpoint flatten_tree (t : tree) : list nat :=
  match t with
  | Node n ts => n :: (fix flatten_trees (l : list tree) : list nat :=
                       match l with
                       | [] => []
                       | t'::l' => flatten_tree t' ++ flatten_trees l'
                       end) ts
  end.

(* END of tree example*)

(* Arbritrary example Starting Here *)
Unset Elimination Schemes.

Inductive arb : Type :=
| A : nat -> arb
| B : nat -> list (nat * arb) -> arb.

Definition arb_rect_helper (P : arb -> Type) (p : nat * arb) : Type :=
  match p with
  | (x, y) => P y
  end.

Definition Forall'' P l := forall (n : nat) (x : arb), In (n,x) l -> P x.

Print In.

Example three_in_list_3_4 : forall (x : nat), In x [3;4] -> (fun x => x > 2) x.
intros.
simpl in *.
destruct H. rewrite <- H. omega.
destruct H. rewrite <- H. omega.
inversion H.
Defined.

Fixpoint arb_rect (P : arb -> Type)
         (H1 : forall (n : nat), P (A n))
         (H2 : forall (n : nat) (l : list (nat * arb)), Forall'' P l -> P (B n l))
         (a : arb) : P a :=
  match a return (P a) with
  | A n => H1 n
  | B n l => let fix loop (l : list (nat * arb)) :=
                 match l with
                 | [] =>
                 | (n',a')::l' =>
                 end
             in
             H2 n l (loop l)
  end.

Definition arb_rec (P : arb -> Set) := arb_rect P.
Definition arb_ind (P : arb -> Prop) := arb_rect P.

Set Elimination Schemes.

Fixpoint size_arb (a : arb) : nat :=
  match a with
  | A _ => 1
  | B _ l => 1 + (fix size_list (l : list (nat * arb)) : nat :=
                   match l with
                   | [] => 0
                   | (_,a')::l' => size_arb a' + size_list l'
                   end) l
  end.

Inductive In' (T : Type) : T -> list T -> Prop :=
| InOne : forall (t : T) (l : list T), In' T t (t::l)
| InMany : forall (t x : T) (l : list T), In' T t l -> In' T t (x::l).

Theorem in_interchangable : forall (T : Type) (t : T) (l : list T),
    In t l <-> In' T t l.
Proof.
  split.
  - induction l.
    + intros. inversion H.
    + intros. inversion H.
      rewrite H0. constructor.
      constructor. apply IHl.
      assumption.
  - induction l.
    + intros; inversion H.
    + intros; inversion H; subst.
      constructor. reflexivity.
      simpl. right. apply IHl.
      assumption.
Qed.

Fixpoint flatten (a : arb) : list nat :=
  match a with
  | A n => [n]
  | B n l => n :: (fix flatten_list (arbs : list (nat * arb)) : list nat :=
                   match arbs with
                   | [] => []
                   | (n',a')::arbs' => n' :: (flatten a' ++ flatten_list arbs')
                end) l
  end.
Obligations.

(* End of arbritrary Example *)

(* Proofs that if something is in a list and that list is a part of another object, *)
(* then the first things is smaller than the second. *)
Lemma size_arb_B_rw : forall (a : arb) (n1 n2 : nat) (l : list (nat * arb)),
size_arb (B n2 ((n1, a) :: l)) = size_arb (B n2 l) + size_arb a.
Proof.
  intros.
  simpl.
  omega.
Qed.

Lemma in_list_less_than : forall (l : list (nat * arb)) (a : arb) (n1 n2 : nat),
    In (n1, a) l ->
    size_arb a < size_arb (B n2 l).
Proof.
  induction l; intros.
  - inversion H.
  - inversion H.
    + subst; clear H; simpl; omega.
    + apply (IHl a0 n1 n2) in H0.
      destruct a. rewrite size_arb_B_rw.
      omega.
Qed.
