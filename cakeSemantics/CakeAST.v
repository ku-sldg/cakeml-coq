Require Import List.
Import ListNotations.
Require Import BinNums.
Require Import String.
Require Import ZArith.BinInt.
Require Import Equations.Equations.

Require Import CakeSem.Utils.
Require Import CakeSem.Namespace.

(* Literal constants *)
Inductive lit : Type :=
  | IntLit : int -> lit
  | CharLit : char -> lit
  | StrLit : string -> lit
  | Word8Lit : word8 -> lit
  | Word64Lit : word64 -> lit.

Inductive opn : Type :=
  | Plus : opn
  | Minus : opn
  | Times : opn
  | Divide : opn
  | Modulo : opn.

Inductive opb : Type :=
  | Lt : opb
  | Gt : opb
  | Leq : opb
  | Geq : opb.

Inductive opw : Type :=
  | Andw : opw
  | Orw : opw
  | Xorw : opw
  | Addw : opw
  | Subw : opw.

Inductive shift : Type :=
  | Lsl : shift
  | Lsr : shift
  | Asr : shift
  | Ror : shift.

Definition modN := string.

Definition varN := string.

Definition conN := string.

Definition typeN := string.

Definition tvarN := string.

Inductive word_size : Type :=
  | W8 : word_size
  | W64 : word_size.


Inductive fpcmp : Type :=
| FP_Less | FP_LessEqual | FP_Greater | FP_GreaterEqual | FP_Equal.

Inductive fpuop : Type :=
| FP_Abs | FP_Neg | FP_Sqrt.

Inductive fpbop : Type :=
| FP_Add | FP_Sub | FP_Mul | FP_Div.

Inductive fptop : Type :=
|  FP_Fma.

Inductive op : Type :=
  | Opapp : op.

Inductive lop : Type :=
  | And : lop
  | Or : lop.

(* Helper relation for lists *)
Inductive Forall'' (A : Type) (P'' : A -> Type) : list A -> Type :=
| Forall_nil'' : Forall'' A P'' []
| Forall_cons'' : forall (x : A) (l : list A), P'' x -> Forall'' A P'' l -> Forall'' A P'' (x :: l).

Arguments Forall'' {A } _.

(* Definition Forall'' {A : Type} (P : A -> Type) (l : list A) := forall (a : A), In a l -> P a. *)

(* We need to build our own inductive principles for a bit *)
Unset Elimination Schemes.

(* Set Elimination Schemes. *)
(** BACKPORT this definition to Cakeml Lem semantics *)
Definition constr_id : Type :=
  option (ident modN conN).

Inductive ast_t : Type :=
  | Atapp : list ast_t -> ident modN typeN -> ast_t.
Derive NoConfusion for ast_t.

Inductive pat : Type :=
  | Pvar : varN -> pat
  | Pcon : constr_id -> list pat -> pat.
Derive NoConfusion for pat.

(* locs Defined elsewhere in the Lem spec *)
Definition locs : Type := list nat.

(* Expressions *)
Inductive exp : Type :=
  | ECon : constr_id -> list exp -> exp
  | EVar : ident modN varN -> exp
  | EFun : varN -> exp -> exp
  | EApp : op -> list exp -> exp
  | EMat : exp -> list (pat * exp) -> exp
  | ELannot : exp -> locs -> exp.
Derive NoConfusion for exp.

Unset Elimination Schemes.

Definition typeDef : Type :=
  list (list tvarN * typeN * list (conN * list ast_t)).

(* Declarations *)
Inductive dec : Type :=
  | Dlet : locs -> pat -> exp -> dec
  | Dletrec : locs -> list (varN * varN * exp) -> dec
  | Dtype : locs -> typeDef -> dec.

Fixpoint pat_bindings (p : pat) : list varN :=
  match p with
  | Pvar n => n :: []
  | Pcon _ ps => List.fold_right (fun p acc => acc ++ pat_bindings p) [] ps
  end.


(*-------------------------------------------------------------------*)
(** Begin induction principle *)

(** AST *)
Fixpoint ast_t_rect' (P : ast_t -> Type)
         (H1 : forall (l : list ast_t) (i : ident modN typeN), Forall'' P l -> P (Atapp l i))
         (a : ast_t) : P a :=
  match a with
  | Atapp l i => let fix F (ls : list ast_t) :=
                   match ls with
                   | [] => Forall_nil'' ast_t P
                   | h::t => Forall_cons'' ast_t P h t (ast_t_rect' P H1 h) (F t)
                   end
               in H1 l i (F l)
  end.

Definition ast_t_ind' (P : ast_t -> Prop) := ast_t_rect' P.
Definition ast_t_rec' (P : ast_t -> Set) := ast_t_rect' P.

(** PAT *)

Fixpoint pat_rect' (P : pat -> Type)
         (H1 : forall (v : varN), P (Pvar v))
         (H2 : forall (o : constr_id) (l : list pat), Forall'' P l -> P (Pcon o l))
         (p : pat) : P p :=
  match p return (P p) with
  | Pvar v => H1 v
  | Pcon o l => let fix loop (l : list pat) :=
                   match l with
                   | [] => Forall_nil'' pat P
                   | h::t => Forall_cons'' pat P h t (pat_rect' P H1 H2 h) (loop t)
                   end
               in
               H2 o l (loop l)
  end.

Definition pat_rec' (P : pat -> Set) := pat_rect' P.
Definition pat_ind' (P : pat -> Prop) := pat_rect' P.


(** Exp *)

Definition exp_rect_helper (P : exp -> Type) (p : pat * exp) : Type :=
  match p with
  | (x, y) => P y
  end.

Definition exp_rect_helper' (P : exp -> Type) (p : varN * varN * exp) : Type :=
  match p with
  | (x, y, z) => P z
  end.

Fixpoint exp_rect' (P : exp -> Type)
         (H1 : forall (o : constr_id) (l : list exp), Forall'' P l
                                                                -> P (ECon o l))
         (H2 : forall (i : ident modN varN), P (EVar i))
         (H3 : forall (v : varN) (e : exp), P e -> P (EFun v e))
         (H4 : forall (o : op) (l : list exp), Forall'' P l -> P (EApp o l))
         (H5 : forall (e : exp), P e -> forall (l : list (pat * exp)), Forall'' (exp_rect_helper P) l
                                                             -> P (EMat e l))
         (H6 : forall (e : exp) (l : locs), P e -> P (ELannot e l))
         (e : exp) : P e :=
  let exp_rect' := fun e' => exp_rect' P H1 H2 H3 H4 H5 H6 e' in
  let fix loop (l : list exp) :=
      match l with
      | [] => Forall_nil'' exp P
      | h::t => Forall_cons'' exp P h t (exp_rect' h) (loop t)
      end
  in
  let fix pair_loop (l : list (pat * exp)) :=
      match l with
      | [] => Forall_nil'' (pat * exp) (exp_rect_helper P)
      | (x,y)::t => Forall_cons'' (pat * exp) (exp_rect_helper P) (x,y) t (exp_rect' y) (pair_loop t)
      end
  in
  let fix trip_loop (l : list (varN * varN * exp)) :=
      match l with
      | [] => Forall_nil'' (varN * varN * exp) (exp_rect_helper' P)
      | (x,y,z)::t => Forall_cons'' (varN * varN * exp) (exp_rect_helper' P) (x,y,z) t (exp_rect' z) (trip_loop t)
      end
  in
  match e with
  | ECon o l  => H1 o l (loop l)
  | EVar i    => H2 i
  | EFun v e' => H3 v e' (exp_rect' e')
  | EApp o l  => H4 o l (loop l)
  | EMat e' l     => H5 e' (exp_rect' e') l (pair_loop l)
  | ELannot e' l  => H6 e' l (exp_rect' e')
  end.

Definition exp_rec' (P : exp -> Set) := exp_rect' P.
Definition exp_ind' (P : exp -> Prop) := exp_rect' P.

Definition list_exp_rect_helper (P : list exp -> Type) (p : pat * exp) : Type :=
  match p with
  | (x, y) => P [y]
  end.

Definition list_exp_rect_helper' (P : list exp -> Type) (p : varN * varN * exp) : Type :=
  match p with
  | (x, y, z) => P [z]
  end.
Print list_rect.

(** DEC *)

Fixpoint dec_rect' (P : dec -> Type)
         (H1 : forall (l : locs) (p : pat) (e : exp), P (Dlet l p e))
         (H2 : forall (l : locs) (lv : list (varN * varN * exp)), P (Dletrec l lv))
         (H3 : forall (l : locs) (t : typeDef), P (Dtype l t))
         (d : dec) : P d :=
  match d with
  | Dlet l p e => H1 l p e
  | Dletrec l lv => H2 l lv
  | Dtype l t => H3 l t
  end.

Definition dec_rec' (P : dec -> Set) := dec_rect' P.
Definition dec_ind' (P : dec -> Prop) := dec_rect' P.

Definition ast_t_rect := ast_t_rect'.
Definition exp_rect := exp_rect'.
Definition pat_rect := pat_rect'.
Definition dec_rect := dec_rect'.

Definition ast_t_rec := ast_t_rec'.
Definition exp_rec := exp_rec'.
Definition pat_rec := pat_rec'.
Definition dec_rec := dec_rec'.

Definition ast_t_ind := ast_t_ind'.
Definition exp_ind := exp_ind'.
Definition pat_ind := pat_ind'.
Definition dec_ind := dec_ind'.
(** End induction principle *)
(*-------------------------------------------------------------------*)

(** Decidable Equality for terms, patterns, and expressions *)
(*-------------------------------------------------------------------*)

Theorem lit_eq_dec (l l' : lit) : {l = l'} + {l <> l'}.
  decide equality; auto with DecidableEquality.  Defined.
Hint Resolve lit_eq_dec : DecidableEquality.

Theorem opn_eq_dec (o o' : opn) : {o = o'} + {o <> o'}.
 decide equality. Defined.
Hint Resolve opn_eq_dec : DecidableEquality.

Theorem opb_eq_dec (o o' : opn) : {o = o'} + {o <> o'}.
  decide equality.
Defined.
Hint Resolve opb_eq_dec : DecidableEquality.

Theorem opw_eq_dec (o o' : opn) : {o = o'} + {o <> o'}.
  decide equality.
Defined.
Hint Resolve opw_eq_dec : DecidableEquality.

Theorem shift_eq_dec (o o' : opn) : {o = o'} + {o <> o'}.
  decide equality.
Defined.
Hint Resolve shift_eq_dec : DecidableEquality.

Theorem op_eq_dec : forall (o0 o1 : op), {o0 = o1} + {o0 <> o1}.
Proof.
  destruct o0.
  destruct o1.
  left.
  reflexivity.
Qed.

Hint Resolve op_eq_dec : DecidableEquality.

Theorem lop_eq_dec : forall (l0 l1 : lop), {l0 = l1} + {l0 <> l1}.
Proof. decide equality.  Defined.
Hint Resolve lop_eq_dec : DecidableEquality.

Theorem ast_t_eq_dec : forall (a1 a2 : ast_t), {a1 = a2} + {a1 <> a2}.
Proof.
  intros.
  apply (ast_t_rect' (fun a1 => forall a2, {a1 = a2} + {a1 <> a2})).
  intros.
  destruct a0.
  destruct (ident_eq_dec _ _ string_dec string_dec i i0).
  rewrite e.
  generalize dependent l0.
  induction X;
  destruct l0;
    try (left; congruence);
    try (right; congruence).
  destruct (p a).
  destruct (IHX l0).
  inv e1.
  subst.
  left; congruence.
  subst.
  right; congruence.
  right; congruence.
  right; congruence.
Defined.
Hint Resolve ast_t_eq_dec : DecidableEquality.

Theorem constr_id_eq_dec : forall (c0 c1 : constr_id), {c0 = c1} + {c0 <> c1}.
Proof.
  decide equality. auto with DecidableEquality.  Defined.
Hint Resolve constr_id_eq_dec : DecidableEquality.

Theorem pat_eq_dec : forall (p0 p1 : pat), {p0 = p1} + {p0 <> p1}.
Proof.
  induction p0 using pat_rect'; destruct p1; try (right; congruence).
  destruct (string_dec v v0); try (subst; left; congruence); try (right; congruence).
  generalize dependent l0.
  induction X; destruct l0; try (right; congruence).
  destruct (constr_id_eq_dec o c); subst.
  left; congruence.
  right; congruence.
  destruct (p p0); try (right; congruence).
  destruct (IHX l0); try (right; congruence).
  inv e0.
  left; reflexivity.
Defined.
Hint Resolve pat_eq_dec : DecidableEquality.

Theorem typeDef_eq_dec : forall (t0 t1 : typeDef), {t0 = t1} + {t0 <> t1}.
Proof. decide equality. decide equality.
       apply list_eq_dec; decide equality; auto with DecidableEquality.
       auto with DecidableEquality.  Defined.
Hint Resolve typeDef_eq_dec : DecidableEquality.

Theorem locs_eq_dec : forall (l0 l1 : locs), {l0 = l1} + {l0 <> l1}.
Proof.
  decide equality.
  auto with DecidableEquality.
Defined.
Hint Resolve locs_eq_dec : DecidableEquality.

Ltac tryr := try (right; congruence).
Ltac tryl := try (left; congruence).

Theorem exp_eq_dec : forall (e0 e1 : exp), {e0 = e1} + {e0 <> e1}.
Proof.
  induction e0 using exp_rect'; destruct e1; try (right; congruence).
  - destruct (constr_id_eq_dec o c); try (right; congruence).
    generalize dependent l0.
    induction X; destruct l0; try (right; congruence).
    subst; left; congruence.
    destruct (IHX l0); try (right; congruence).
    destruct (p e0); try (right; congruence).
    inv e1. left; reflexivity.
  - destruct (ident_eq_dec _ _ string_dec string_dec i i0); subst.
    left; congruence.
    right; congruence.
  - destruct (string_dec v v0); tryr.
    destruct (IHe0 e1); tryr.
    tryl.
  - generalize dependent l0.
    destruct (op_eq_dec o o0); tryr.
    induction X; intros; destruct l0; tryr.
    subst; tryl.
    destruct (IHX l0); tryr.
    destruct (p e0); tryr.
    inv e1; subst.
    tryl.
  - generalize dependent l0.
    destruct (IHe0 e1); tryr.
    induction X; destruct l0; tryr.
    subst; tryl.
    destruct (IHX l0); tryr.
    destruct x.
    destruct p0.
    simpl in *.
    destruct (p e4); tryr.
    destruct (pat_eq_dec p1 p0); tryr.
    subst; inv e2; tryl.
  - destruct (locs_eq_dec l l0); tryr.
    destruct (IHe0 e1); tryr.
    subst; tryl.
Qed.
Hint Resolve exp_eq_dec : DecidableEquality.
Instance EqDec_exp : EqDec exp := exp_eq_dec.

Print EqDec_exp.

Theorem dec_eq_dec : forall (d0 d1 : dec), {d0 = d1} + {d0 <> d1}.
Proof.
  decide equality; try (auto with DecidableEquality).
Defined.
Hint Resolve dec_eq_dec : DecidableEquality.

(*-------------------------------------------------------------------*)
