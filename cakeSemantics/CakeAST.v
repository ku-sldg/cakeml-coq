Require Import List.
Import ListNotations.
Require Import BinNums.
Require Import String.
Require Import ZArith.BinInt.

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

(** BACKPORT this definition to Cakeml Lem semantics *)
Definition constr_id : Type :=
  option (ident modN conN).

Inductive ast_t : Type :=
  | Atapp : list ast_t -> ident modN typeN -> ast_t.

Inductive pat : Type :=
  | Pvar : varN -> pat
  | Pcon : constr_id -> list pat -> pat.

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

Set Elimination Schemes.

(* Inductive is_subexp : exp -> list exp -> Prop := *)
(* | ReflexiveSubexp : forall (e : exp), is_subexp e [e] *)
(* | ListSubexp : forall (e e' : exp) (l : list exp), *)
(*     is_subexp e [e'] \/ is_subexp e l -> *)
(*     is_subexp e (e'::l) *)
(* | ECon_subexp : forall (cid : constr_id) (e : exp) (l : list exp), *)
(*     is_subexp e l -> *)
(*     is_subexp e [ECon cid l] *)
(* | EFun_subexp : forall (v : varN) (e1 e2 : exp), *)
(*     is_subexp e1 [e2] -> *)
(*     is_subexp e1 [EFun v e2] *)
(* | EApp_subexp : forall (e : exp) (o : op) (l : list exp), *)
(*     is_subexp e l -> *)
(*     is_subexp e [EApp o l] *)
(* | EMat_subexp : forall (e1 e2 : exp) (l : list (pat * exp)), *)
(*     is_subexp e1 [e2] \/ is_subexp e1 (map snd l) -> *)
(*     is_subexp e1 [EMat e2 l] *)
(* | ELannot_subexp : forall (e1 e2 : exp) (lcs : locs), *)
(*     is_subexp e1 [e2] -> *)
(*     is_subexp e1 [ELannot e2 lcs]. *)

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
Fixpoint ast_t_rect (P : ast_t -> Type)
         (H1 : forall (l : list ast_t) (i : ident modN typeN), Forall'' P l -> P (Atapp l i))
         (a : ast_t) : P a :=
  match a with
  | Atapp l i => let fix F (ls : list ast_t) :=
                   match ls with
                   | [] => Forall_nil'' ast_t P
                   | h::t => Forall_cons'' ast_t P h t (ast_t_rect P H1 h) (F t)
                   end
               in H1 l i (F l)
  end.

Definition ast_t_ind (P : ast_t -> Prop) := ast_t_rect P.
Definition ast_t_rec (P : ast_t -> Set) := ast_t_rect P.

(** PAT *)

Fixpoint pat_rect (P : pat -> Type)
         (H1 : forall (v : varN), P (Pvar v))
         (H2 : forall (o : constr_id) (l : list pat), Forall'' P l -> P (Pcon o l))
         (p : pat) : P p :=
  match p return (P p) with
  | Pvar v => H1 v
  | Pcon o l => let fix loop (l : list pat) :=
                   match l with
                   | [] => Forall_nil'' pat P
                   | h::t => Forall_cons'' pat P h t (pat_rect P H1 H2 h) (loop t)
                   end
               in
               H2 o l (loop l)
  end.

Definition pat_rec (P : pat -> Set) := pat_rect P.
Definition pat_ind (P : pat -> Prop) := pat_rect P.


(** Exp *)

Definition exp_rect_helper (P : exp -> Type) (p : pat * exp) : Type :=
  match p with
  | (x, y) => P y
  end.

Definition exp_rect_helper' (P : exp -> Type) (p : varN * varN * exp) : Type :=
  match p with
  | (x, y, z) => P z
  end.

Fixpoint exp_rect (P : exp -> Type)
         (H1 : forall (o : constr_id) (l : list exp), Forall'' P l
                                                                -> P (ECon o l))
         (H2 : forall (i : ident modN varN), P (EVar i))
         (H3 : forall (v : varN) (e : exp), P e -> P (EFun v e))
         (H4 : forall (o : op) (l : list exp), Forall'' P l -> P (EApp o l))
         (H5 : forall (e : exp), P e -> forall (l : list (pat * exp)), Forall'' (exp_rect_helper P) l
                                                             -> P (EMat e l))
         (H6 : forall (e : exp) (l : locs), P e -> P (ELannot e l))
         (e : exp) : P e :=
  let exp_rect' := fun e' => exp_rect P H1 H2 H3 H4 H5 H6 e' in
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

Definition exp_rec (P : exp -> Set) := exp_rect P.
Definition exp_ind (P : exp -> Prop) := exp_rect P.

(** DEC *)

Fixpoint dec_rect (P : dec -> Type)
         (H1 : forall (l : locs) (p : pat) (e : exp), P (Dlet l p e))
         (H2 : forall (l : locs) (lv : list (varN * varN * exp)), P (Dletrec l lv))
         (H3 : forall (l : locs) (t : typeDef), P (Dtype l t))
         (d : dec) : P d :=
  match d with
  | Dlet l p e => H1 l p e
  | Dletrec l lv => H2 l lv
  | Dtype l t => H3 l t
  end.

Definition dec_rec (P : dec -> Set) := dec_rect P.
Definition dec_ind (P : dec -> Prop) := dec_rect P.


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
Proof. repeat decide equality.  Defined.
Hint Resolve op_eq_dec : DecidableEquality.

Theorem lop_eq_dec : forall (l0 l1 : lop), {l0 = l1} + {l0 <> l1}.
Proof. decide equality.  Defined.
Hint Resolve lop_eq_dec : DecidableEquality.

Theorem ast_t_eq_dec : forall (a1 a2 : ast_t), {a1 = a2} + {a1 <> a2}.
Proof.
  decide equality; auto with DecidableEquality; try (apply ident_eq_dec; apply string_dec);
  generalize dependent l0.
  induction l; destruct l0;
    try (left; reflexivity);
    try (right; discriminate).
  inv H.
  destruct (H2 a0); destruct (IHl H3 l0);
    try (left; congruence);
    try (right; congruence).
Defined.
Hint Resolve ast_t_eq_dec : DecidableEquality.

Theorem constr_id_eq_dec : forall (c0 c1 : constr_id), {c0 = c1} + {c0 <> c1}.
Proof.
  decide equality. auto with DecidableEquality.  Defined.
Hint Resolve constr_id_eq_dec : DecidableEquality.

Theorem pat_eq_dec : forall (p0 p1 : pat), {p0 = p1} + {p0 <> p1}.
Proof. decide equality; auto with DecidableEquality.
       generalize dependent l0.
       induction l; destruct l0; try (left; reflexivity); try (right; discriminate).
       inv X.
       destruct (X0 p); destruct (IHl X1 l0);
         try (left; congruence);
         try (right; congruence).
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


Theorem exp_eq_dec : forall (e0 e1 : exp), {e0 = e1} + {e0 <> e1}.
Proof.
  decide equality; auto with DecidableEquality;
    try (decide equality; try (apply ident_eq_dec); apply string_dec); generalize dependent l0.

  - induction l; destruct l0.
    + left; reflexivity.
    + right; congruence.
    + right; congruence.
    + inv X.
      destruct (X0 e); destruct (IHl X1 l0);
        try (left; congruence);
        try (right; congruence).

  - induction l; destruct l0.
    + left; reflexivity.
    + right; congruence.
    + right; congruence.
    + inv X; subst.
      * destruct (X0 e); destruct (IHl X1 l0); subst;
          try (left; reflexivity);
          try (right; congruence).
  - induction l; destruct l0;
      try (left; reflexivity);
      try (right; congruence).
    inv X0.
    destruct a0 as [ap ae]; destruct p as [pp pe]; destruct (pat_eq_dec ap pp);
      destruct (X1 pe); destruct (IHl X2 l0); subst;
        try (left; reflexivity);
        try (right; congruence).
Qed.

Hint Resolve exp_eq_dec : DecidableEquality.

Theorem dec_eq_dec : forall (d0 d1 : dec), {d0 = d1} + {d0 <> d1}.
Proof.
  decide equality; try (auto with DecidableEquality).
Defined.
Hint Resolve dec_eq_dec : DecidableEquality.

(*-------------------------------------------------------------------*)
