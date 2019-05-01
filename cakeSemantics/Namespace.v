Require Import Coq.Lists.List.
Import ListNotations.
Require Import Structures.Equalities.
Require Import Classes.EquivDec.
Require Import Program.Utils.

Definition alist (X Y : Type) := list (X * Y).

(* Comes from somewhere else in Lem semantics *)
Inductive ident (X:Type) (Y:Type) : Type :=
| Short : Y -> ident X Y
| Long : X -> ident X Y -> ident X Y.

Theorem ident_eq_dec : forall (X Y : Type) (i0 i1 : ident X Y),
    (forall (x0 x1 : X), {x0 = x1} + {x0 <> x1}) ->
    (forall (y0 y1 : Y), {y0 = y1} + {y0 <> y1}) -> {i0 = i1} + {i0 <> i1}.
Proof. decide equality.  Qed.

Instance ident_equiv_dec_inst (M N : Type) `(eqm : EqDec M eq) `(eqn : EqDec N eq) : EqDec (ident M N) eq :=
  { equiv_dec :=
      fix aux (x y : ident M N) :=
        match x,y with
        | Short _ _ n, Short _ _ n' => if equiv_dec n n' then in_left else in_right
        | Long _ _ m id, Long _ _ m' id' => if equiv_dec m m' then
                                             if aux id id' then in_left else in_right
                                           else in_right
        | _, _ => in_right
        end
  }.
rewrite e. reflexivity. intros C. inversion C. apply (c H0).
discriminate. discriminate.
rewrite e, e0. reflexivity. intros C. inversion C. apply (c H1).
intros C. inversion C. apply (c H0).  Qed.

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

Section NamespaceDec.
  Variable M : Type.
  Variable N : Type.
  Variable V : Type.
  Hypothesis HM : forall (m0 m1 : M), {m0 = m1} + {m0 <> m1}.
  Hypothesis HN : forall (n0 n1 : N), {n0 = n1} + {n0 <> n1}.
  Hypothesis HV : forall (v0 v1 : V), {v0 = v1} + {v0 <> v1}.

  Theorem namespace_eq_dec : forall (n0 n1 : namespace M N V), {n0 = n1} + {n0 <> n1}.
  Proof. decide equality. decide equality. apply ident_eq_dec. apply HM. apply HN.  Qed.
End NamespaceDec.

Fixpoint lookup {X Y : Type} `{EqDec X} (x : X) (l : alist X Y) : option Y :=
  match l with
  | [] => None
  | (x',y) :: l' => if equiv_dec x x' then Some y else lookup x l'
  end.

Fixpoint get_modded_namespace {M N V : Type} `{EqDec M} (m : M) (ns : namespace M N V) : namespace M N V :=
  match ns with
  | [] => []
  | (i,v) :: ns' => match i with
                    | Short _ => get_modded_namespace m ns'
                    | Long m' i' => if equiv_dec m m'
                                   then (i',v) :: (get_modded_namespace m ns')
                                   else get_modded_namespace m ns'
                  end
  end.

Fixpoint nsLookup {M N V : Type} `{EqDec M eq} `{EqDec N eq} (id : ident M N) (ns : namespace M N V) : option V :=
  match id with
  | Short n => lookup id ns
  | Long m id' => nsLookup id' (get_modded_namespace m ns)
  end.

Fixpoint nsLookupMod {M N V : Type} `{EqDec M} `{EqDec N} (ns : namespace M N V) (xs : list M) : option (namespace M N V) :=
  match xs, ns with
  | _, [] => None
  | [], ns => Some ns
  | m :: ms, ns => nsLookupMod (filter (fun i => match fst i with
                                            | Short n    => false
                                            | Long  m' n => if equiv_dec m m' then true else false
                                            end)
                                     ns)
                             ms
  end.

Definition nsEmpty {M N V : Type} := @nil ((ident M N) * V).

Definition nsAppend {M N V : Type} (ns1 : namespace M N V) (ns2 : namespace M N V) : namespace M N V :=
  ns1 ++ ns2.

Definition nsLift {M N V : Type} (m : M) (ns : namespace M N V) : namespace M N V :=
  map (fun i => (Long m (fst i), snd i)) ns.

Definition alist_to_ns {M N V : Type} (l : alist N V) : namespace M N V :=
  map (fun i => (Short (fst i), snd i)) l.

Definition nsBind {M N V : Type} (n : N) (v : V) (ns : namespace M N V) : namespace M N V :=
  (Short n, v) :: ns.

Definition nsBindList {M N V : Type} (l : alist N V) (ns : namespace M N V) : namespace M N V :=
  nsAppend (alist_to_ns l) ns.

Definition nsOptBind {M N V : Type} (n : option N) (v : V) (ns : namespace M N V) : namespace M N V :=
  match n with
  | None => ns
  | Some n' => nsBind n' v ns
  end.

Definition nsSing {M N V : Type} (n : N) (v : V) : namespace M N V := [(Short n, v)].

(* First difference here. Using Prop instead of bool. *)
Definition nsSub {M N V1 V2 : Type} `{EqDec M eq} `{EqDec N eq} `{EqDec V1 eq} `{EqDec V2 eq}
           (rel : ident M N -> V1 -> V2 -> Prop)
           (ns1 : namespace M N V1)
           (ns2 : namespace M N V2) : Prop :=
  (forall (id : ident M N) (v1 : V1), nsLookup id ns1 = Some v1 -> exists (v2 : V2), nsLookup id ns2 = Some v2 /\ rel id v1 v2)
  /\
  (forall (id : ident M N), nsLookup id ns1 = None -> nsLookup id ns2 = None).

Definition nsAll {M N V : Type} `{EqDec M eq} `{EqDec N eq} `{EqDec V}
           (rel : ident M N -> V -> Prop)
           (ns : namespace M N V) : Prop :=
  (forall (id : ident M N) (v : V),
     nsLookup id ns = Some v -> rel id v).

Definition eAll2 {M N V1 V2 : Type} `{EqDec M eq} `{EqDec N eq} `{EqDec V1 eq} `{EqDec V2 eq}
(rel : ident M N -> V1 -> V2 -> Prop) (ns1 : namespace M N V1) (ns2 : namespace M N V2) : Prop :=
  nsSub rel ns1 ns2 /\ nsSub (fun x y z => rel x z y) ns2 ns1.

(* Need to construct a set of id's that are bound. *)

(* Definition nsDom {M N V : Type} `{Eq M} `{Eq N} `{Eq V} SetType V (ns : namespace M N V) : set (Id M N) := *)

 (*  nsLookup ns id = Just v *)
 (* { n | forall (v IN universal) (n IN universal) | nsLookup env n = Just v } *)

Definition extractIds {M N V : Type} (ns : namespace M N V) : list (ident M N) := map fst ns.

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

(* Definition nsDomMod : {M N V : Type} `{Eq M} `{Eq N} `{Eq V} SetType V (ns : namespace M N V) : set (list M) := *)

(* let nsDomMod env = { n | forall (v IN universal) (n IN universal) | nsLookupMod env n = Just v } *)

Fixpoint nsMap {M N V W : Type} (f : V -> W)
         (ns : namespace M N V) : namespace M N W :=
  map (fun i => (fst i, f (snd i))) ns.
