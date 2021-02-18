Require Import Coq.Lists.List.
Import ListNotations.
Require Import Structures.Equalities.
Require Import Classes.EquivDec.
Require Import Program.Utils.
Require Import CakeSem.Utils.

Definition alist (X Y : Type) := list (X * Y).

Fixpoint range {K V : Type} (l : alist K V) : list V :=
  match l with
  | [] => []
  | (k,v)::l' => v::(range l')
  end.

(* Comes from somewhere else in Lem semantics *)
Inductive ident (X:Type) (Y:Type) : Type :=
  | Short : Y -> ident X Y
  | Long : X -> ident X Y -> ident X Y.

Arguments Short {X} {Y}.
Arguments Long {X} {Y}.

Fixpoint mk_id {M N: Type} (l : list M) (n : N) : ident M N :=
  match l with
  | [] => Short n
  | h :: t => Long h (mk_id t n)
  end.

Fixpoint id_to_n {M N : Type} (id : ident M N) : N :=
  match id with
  | Short n    => n
  | Long x id' => id_to_n id'
  end.

Fixpoint id_to_mods {M N : Type} (id : ident M N) : list M :=
  match id with
  | Short _ => []
  | Long m id' => m :: id_to_mods id'
  end.

Definition namespace (M N V : Type) := alist (ident M N) V.

Definition nsEmpty {M N V : Type} :=
  @nil ((ident M N) * V).

(* Namespace functions using a sumbool type for equality tests *)
Fixpoint lookup {X Y : Type} (f : forall (x1 x2 : X), {x1 = x2} + {x1 <> x2}) (x : X) (l : alist X Y) : option Y :=
  match l with
  | [] => None
  | (x',y) :: l' => if f x x' then Some y else lookup f x l'
  end.

Fixpoint get_modded_namespace {M N V : Type} (f : forall (x1 x2 : M), {x1 = x2} + {x1 <> x2})
         (m : M) (ns : namespace M N V) : namespace M N V :=
  match ns with
  | [] => []
  | (i,v) :: ns' => match i with
                    | Short _ => get_modded_namespace f m ns'
                    | Long m' i' => if f m m'
                                   then (i',v) :: (get_modded_namespace f m ns')
                                   else get_modded_namespace f m ns'
                  end
  end.

Definition nsLookup {M N V : Type} (f : forall (x1 x2 : ident M N), {x1 = x2} + {x1 <> x2})
           (id : ident M N) (ns : namespace M N V) : option V := lookup f id ns.

Fixpoint nsLookupMod {M N V : Type} (f_dec : forall m1 m2 : M, {m1 = m2} + {m1 <> m2})
         (ns : namespace M N V) (xs : list M): option (namespace M N V) :=
  match xs, ns with
  | _, [] => None
  | [], ns => Some ns
  | m :: ms, ns => nsLookupMod f_dec
                             (filter (fun '(i1,i2) => match i1 with
                                                   | Short n    => false
                                                   | Long  m' n => if f_dec m m' then true else false
                                                   end)
                                     ns)
                             ms
  end.

Definition nsAppend {M N V : Type} (ns1 : namespace M N V) (ns2 : namespace M N V) : namespace M N V :=
  ns1 ++ ns2.

Definition nsLift {M N V : Type} (m : M) (ns : namespace M N V) : namespace M N V :=
  map (fun '(i1,i2) => (Long m i1, i2)) ns.

Definition alist_to_ns {M N V : Type} (l : alist N V) : namespace M N V :=
  map (fun '(i1,i2) => (Short i1, i2)) l.

Definition nsBind {M N V : Type} (n : N) (v : V) (ns : namespace M N V) : namespace M N V :=
  (Short n, v) :: ns.

Definition nsBindList {M N V : Type} (l : alist N V) (ns : namespace M N V) : namespace M N V :=
  nsAppend (alist_to_ns l) ns.

Definition nsOptBind {M N V : Type} (n : option N) (v : V) (ns : namespace M N V) : namespace M N V :=
  match n with
  | None => ns
  | Some n' => nsBind n' v ns
  end.

Definition nsSing {M N V : Type} (n : N) (v : V) : namespace M N V :=
  [(Short n, v)].

(* LATER: fix this difference *)
(* First difference here. Using Prop instead of bool. *)
Definition nsSub {M N V1 V2 : Type}
           (dec : forall (x y : ident M N), {x=y} + {x<>y})
           (rel : ident M N -> V1 -> V2 -> Prop)
           (ns1 : namespace M N V1)
           (ns2 : namespace M N V2) : Prop :=
     (forall (id : ident M N) (v1 : V1), nsLookup dec id ns1 = Some v1 ->
       exists (v2 : V2), nsLookup dec id ns2 = Some v2 /\ rel id v1 v2)
  /\ (forall (id : ident M N), nsLookup dec id ns1 = None -> nsLookup dec id ns2 = None).

Definition nsAll {M N V : Type} (dec : forall (x y : ident M N), {x=y} + {x<>y})
           (rel : ident M N -> V -> Prop)
           (ns : namespace M N V) : Prop :=
  (forall (id : ident M N) (v : V),
     nsLookup dec id ns = Some v -> rel id v).

(* Definition eAll2 {M N V1 V2 : Type} (rel : ident M N -> V1 -> V2 -> Prop) *)
(*   (ns1 : namespace M N V1) (ns2 : namespace M N V2) : Prop := *)
(*   nsSub rel ns1 ns2 /\ nsSub (fun x y z => rel x z y) ns2 ns1. *)

Definition nsAll2 {M N V1 V2 : Type} (dec : forall (x y : ident M N), {x=y} + {x<>y})
           (rel : ident M N -> V1 -> V2 -> Prop)
           (ns1 : namespace M N V1)
           (ns2 : namespace M N V2) : Prop :=
  nsSub dec rel ns1 ns2 /\
  nsSub dec (fun x y z => rel x z y) ns2 ns1.

Definition extractIds {M N V : Type} (ns : namespace M N V) : list (ident M N) :=
  map fst ns.

Fixpoint extractMods {M N V : Type} (ns : namespace M N V) : list (list M) :=
  let get_ids := fix gids id :=
                   match id with
                   | Short _ => []
                   | Long m id' => m :: gids id'
                   end
  in
  match ns with
  | [] => []
  | (id,_)::ns' => get_ids id :: extractMods ns'
  end.

Fixpoint nsMap {M N V W : Type} (f : V -> W)
         (ns : namespace M N V) : namespace M N W :=
  map (fun '(i1,i2) => (i1, f i2)) ns.

(* Namespace Theorems *)
Section NamespaceDec.
  Variable M : Type.
  Variable N : Type.
  Variable V : Type.
  Variable m_dec : forall (m0 m1 : M), {m0 = m1} + {m0 <> m1}.
  Variable n_dec : forall (n0 n1 : N), {n0 = n1} + {n0 <> n1}.
  Variable v_dec : forall (v0 v1 : V), {v0 = v1} + {v0 <> v1}.

  Theorem ident_eq_dec : forall (i0 i1 : ident M N),
      {i0 = i1} + {i0 <> i1}.
  Proof. decide equality.  Defined.

  Theorem namespace_eq_dec : forall (n0 n1 : namespace M N V), {n0 = n1} + {n0 <> n1}.
  Proof. decide equality. decide equality. apply ident_eq_dec. Defined.
End NamespaceDec.
Hint Resolve namespace_eq_dec : DecidableEquality.
Hint Resolve ident_eq_dec : DecidableEquality.

Section LookupTheory.
  Variable N : Type.
  Variable V : Type.
  Variable n_dec : forall (n0 n1 : N), {n0 = n1} + {n0 <> n1}.

  Lemma lookup_cover : forall (n : N) (ns ns' : alist N V) (v : V),
      lookup n_dec n ns  = Some v ->
      lookup n_dec n (ns ++ ns') = lookup n_dec n ns.
  Proof.
    intros n ns ns' v.
    generalize dependent ns'.
    induction ns; intros ns' H.
    - inversion H.
    - destruct a. simpl. simpl in H. destruct n_dec.
      + reflexivity.
      + apply IHns. assumption.
  Qed.

  Lemma lookup_drop : forall (id : N) (ns ns' : alist N V),
      lookup n_dec id ns = None ->
      lookup n_dec id (ns ++ ns') = lookup n_dec id ns'.
  Proof.
    intros id ns.
    induction ns; intros ns' H.
    - reflexivity.
    - destruct a; simpl in *. destruct n_dec.
      + inversion H.
      + apply IHns. assumption.
  Qed.

  Lemma lookup_same : forall (n : N) (ns : alist N V),
      lookup n_dec n (ns ++ ns) = lookup n_dec n ns.
  Proof.
    intros n ns.
    destruct (lookup n_dec n ns) eqn:H; rewrite <- H.
    - apply lookup_cover with v; assumption.
    - apply lookup_drop; assumption.
  Qed.
End LookupTheory.

Section NamespaceTheory.
  Variable M : Type.
  Variable N : Type.
  Variable V : Type.
  Variable m_dec : forall (m0 m1 : M), {m0 = m1} + {m0 <> m1}.
  Variable n_dec : forall (n0 n1 : N), {n0 = n1} + {n0 <> n1}.
  Variable v_dec : forall (v0 v1 : V), {v0 = v1} + {v0 <> v1}.

  Definition id_dec := ident_eq_dec M N m_dec n_dec.

  Lemma get_modded_namespace_append : forall (ns ns' : namespace M N V) (x : M),
      get_modded_namespace m_dec x (ns ++ ns') = (get_modded_namespace m_dec x ns) ++ (get_modded_namespace m_dec x ns').
  Proof.
    induction ns; intros ns' x.
    - reflexivity.
    - destruct a. destruct i.
      + apply IHns.
      + simpl. destruct (m_dec x m).
        * simpl. rewrite IHns. reflexivity.
        * simpl. apply IHns.
  Qed.

  Lemma nsLookup_cover : forall (id : ident M N) (ns ns' : namespace M N V) (v : V),
      nsLookup id_dec id ns = Some v ->
      nsLookup id_dec id (ns ++ ns') = nsLookup id_dec id ns.
  Proof.
    intros. unfold nsLookup in *. apply lookup_cover with v. assumption.
  Qed.

  Lemma nsLookup_drop : forall (id : ident M N) (ns ns' : namespace M N V),
      nsLookup id_dec id ns = None ->
      nsLookup id_dec id (ns ++ ns') = nsLookup id_dec id ns'.
  Proof.
    intros id ns ns' H.
    unfold nsLookup in *. apply lookup_drop. assumption.
  Qed.

  Lemma nsLookup_same : forall (id : ident M N) (ns : namespace M N V),
      nsLookup id_dec id (ns ++ ns) = nsLookup id_dec id ns.
  Proof.
    intros id ns.
    unfold nsLookup in *. apply lookup_same.
  Qed.

End NamespaceTheory.
