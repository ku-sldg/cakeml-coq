Require Import List.
Import ListNotations.
Require Import BinNums.
Require Import String.
Require Import ZArith.BinInt.
Require Import Equations.

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
  | Opn : opn -> op
  | Opb : opb -> op
  | Opw : word_size -> opw -> op
  | Shift : word_size -> shift -> nat -> op
  | Equality : op
  | OpFpCmp : fpcmp -> op
  | OpFpUop : fpuop -> op
  | OpFpBop : fpbop -> op
  | OpFpTop : fptop -> op
(* Function application *)
  | Opapp : op
  (* Reference operations *)
  | Opassign : op
  | Opref : op
  | Opderef : op
  (* Word8Array operations *)
  | Aw8alloc : op
  | Aw8sub : op
  | Aw8length : op
  | Aw8update : op
  (* Word/integer conversions *)
  | WordFromInt : word_size -> op
  | WordToInt : word_size -> op
  (* string/bytearray conversions *)
  | CopyStrStr : op
  | CopyStrAw8 : op
  | CopyAw8Str : op
  | CopyAw8Aw8 : op
  (* Char operations *)
  | Ord : op
  | Chr : op
  | Chopb : opb -> op
  (* String operations *)
  | Implode : op
  | Explode : op
  | Strsub : op
  | Strlen : op
  | Strcat : op
  (* Vector operations *)
  | VfromList : op
  | Vsub : op
  | Vlength : op
  (* Array operations *)
  | Aalloc : op
  | AallocEmpty : op
  | Asub : op
  | Alength : op
  | Aupdate : op
  (* Unsafe array accesses *)
  | Asub_unsafe : op
  | Aupdate_unsafe : op
  | Aw8sub_unsafe : op
  | Aw8update_unsafe : op
  (* List operations *)
  | ListAppend : op
  (* Configure the GC *)
  | ConfigGC : op
  (* Call a given foreign function *)
  | FFI : string -> op.

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
  | Atvar : tvarN -> ast_t
  | Atfun : ast_t -> ast_t -> ast_t
  | Attup : list ast_t -> ast_t
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
  | ERaise : exp -> exp
  | EHandle : exp -> list (pat * exp) -> exp
  | ELit : lit -> exp
  | ECon : constr_id -> list exp -> exp
  | EVar : ident modN varN -> exp
  | EFun : varN -> exp -> exp
  | EApp : op -> list exp -> exp
  | ELog : lop -> exp -> exp -> exp
  | EIf  : exp -> exp -> exp -> exp
  | EMat : exp -> list (pat * exp) -> exp
  | ELet : option varN -> exp -> exp -> exp
  | ELetrec : list (varN * varN * exp) -> exp -> exp
  | ELannot : exp -> locs -> exp.
Derive NoConfusion for exp.

Unset Elimination Schemes.

Definition typeDef : Type :=
  list (list tvarN * typeN * list (conN * list ast_t)).

(* Declarations *)
Inductive dec : Type :=
  | Dlet : locs -> pat -> exp -> dec
  | Dletrec : locs -> list (varN * varN * exp) -> dec
  | Dtype : locs -> typeDef -> dec
  | Dtabbrev : locs -> list tvarN -> typeN -> ast_t -> dec
  | Dexn : locs -> conN -> list ast_t -> dec
  | Dmod : modN -> list dec -> dec
  | Dlocal : list dec -> list dec -> dec.

Fixpoint pat_bindings (p : pat) : list varN :=
  match p with
  | Pvar n => n :: []
  | Pcon _ ps => List.fold_right (fun p acc => acc ++ pat_bindings p) [] ps
  end.


(*-------------------------------------------------------------------*)
(** Begin induction principle *)

(** AST *)
Fixpoint ast_t_rect' (P : ast_t -> Type)
         (H1 : forall (s : tvarN), P (Atvar s))
         (H2 : forall (a1 a2 : ast_t), P a1 -> P a2 -> P (Atfun a1 a2))
         (H3 : forall (l : list ast_t), Forall'' P l -> P (Attup l))
         (H4 : forall (l : list ast_t) (i : ident modN typeN), Forall'' P l -> P (Atapp l i))
         (a : ast_t) : P a :=
  let fix loop (ls : list ast_t) :=
      match ls with
      | [] => Forall_nil'' ast_t P
      | h::t => Forall_cons'' ast_t P h t (ast_t_rect' P H1 H2 H3 H4 h) (loop t)
      end
  in
  match a with
  | Atvar s => H1 s
  | Atfun a1 a2 => H2 a1 a2 (ast_t_rect' P H1 H2 H3 H4 a1) (ast_t_rect' P H1 H2 H3 H4 a2)
  | Attup l => H3 l (loop l)
  | Atapp l i =>  H4 l i (loop l)
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
         (H  : forall (e' : exp), P e' -> P (ERaise e'))
         (H0 : forall (e' : exp) (l : list (pat * exp)), P e' ->
                                                    Forall'' (exp_rect_helper P) l ->
                                                    P (EHandle e' l))
         (H1 : forall (l : lit), P (ELit l))
         (H2 : forall (o : constr_id) (l : list exp), Forall'' P l ->
                                                 P (ECon o l))
         (H3 : forall (i : ident modN varN), P (EVar i))
         (H4 : forall (v : varN) (e : exp), P e -> P (EFun v e))
         (H5 : forall (o : op) (l : list exp), Forall'' P l -> P (EApp o l))
         (H6 : forall (lo : lop) (e1 e2 : exp), P e1 -> P e2 -> P (ELog lo e1 e2))
         (H7 : forall (c t e : exp), P c -> P t -> P e -> P (EIf c t e))
         (H8 : forall (e : exp), P e -> forall (l : list (pat * exp)), Forall'' (exp_rect_helper P) l ->
                                                            P (EMat e l))
         (H9 : forall (o : option varN) (e1 e2 : exp), P e1 -> P e2 -> P (ELet o e1 e2))
         (H10 : forall (vve : list (varN * varN * exp)) (e : exp), Forall'' (exp_rect_helper' P) vve ->
                                                   P e -> P (ELetrec vve e))
         (H11 : forall (e : exp) (l : locs), P e -> P (ELannot e l))
         (e : exp) : P e :=
  let exp_rect' := fun e' => exp_rect' P H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 e' in
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
  | ERaise e' => H e' (exp_rect' e')
  | EHandle e' l => H0 e' l (exp_rect' e') (pair_loop l)
  | ELit l => H1 l
  | ECon o l  => H2 o l (loop l)
  | EVar i    => H3 i
  | EFun v e' => H4 v e' (exp_rect' e')
  | EApp o l  => H5 o l (loop l)
  | ELog lo e1 e2 => H6 lo e1 e2 (exp_rect' e1) (exp_rect' e2)
  | EIf c t e => H7 c t e (exp_rect' c) (exp_rect' t) (exp_rect' e)
  | EMat e' l     => H8 e' (exp_rect' e') l (pair_loop l)
  | ELet o e1 e2  => H9 o e1 e2 (exp_rect' e1) (exp_rect' e2)
  | ELetrec vve e => H10 vve e (trip_loop vve) (exp_rect' e)
  | ELannot e' l  => H11 e' l (exp_rect' e')
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

(** DEC *)
Fixpoint dec_rect' (P : dec -> Type)
         (H1 : forall (l : locs) (p : pat) (e : exp), P (Dlet l p e))
         (H2 : forall (l : locs) (lv : list (varN * varN * exp)), P (Dletrec l lv))
         (H3 : forall (l : locs) (t : typeDef), P (Dtype l t))
         (H4 : forall (l : locs) (tvs : list tvarN) (tn : typeN) (a : ast_t), P (Dtabbrev l tvs tn a))
         (H5 : forall (l : locs) (cn : conN) (ls : list ast_t), P (Dexn l cn ls))
         (H6 : forall (mn : modN) (ds : list dec), Forall'' P ds -> P (Dmod mn ds))
         (H7 : forall (ds1 ds2 : list dec), Forall'' P ds1 -> Forall'' P ds2 -> P (Dlocal ds1 ds2))
         (d : dec) : P d :=
  let fix loop (l : list dec) : Forall'' P l :=
      match l with
      | [] => Forall_nil'' _ _
      | d'::l' => Forall_cons'' _ P d' l' (dec_rect' P H1 H2 H3 H4 H5 H6 H7 d') (loop l')
      end
  in
  match d with
  | Dlet l p e => H1 l p e
  | Dletrec l lv => H2 l lv
  | Dtype l t => H3 l t
  | Dtabbrev l tvs tn a => H4 l tvs tn a
  | Dexn l cn ls => H5 l cn ls
  | Dmod mn ds => H6 mn ds (loop ds)
  | Dlocal ds1 ds2 => H7 ds1 ds2 (loop ds1) (loop ds2)
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
  decide equality.
  - decide equality.
  - decide equality.
  - decide equality.
  - decide equality.
  - decide equality.
  - decide equality.
  - decide equality.
  - decide equality.
  - decide equality.
  - decide equality.
  - destruct f. destruct f0. left. reflexivity.
  - decide equality.
  - decide equality.
  - decide equality.
  - apply string_dec.
Defined.

Hint Resolve op_eq_dec : DecidableEquality.

Theorem lop_eq_dec : forall (l0 l1 : lop), {l0 = l1} + {l0 <> l1}.
Proof. decide equality.  Defined.
Hint Resolve lop_eq_dec : DecidableEquality.

Theorem ast_t_eq_dec : forall (a1 a2 : ast_t), {a1 = a2} + {a1 <> a2}.
Proof.
  decide equality.
  - apply string_dec.
  - generalize dependent l0. induction X; destruct l0.
    left; reflexivity.
    right; congruence.
    right; congruence.
    destruct (IHX l0). destruct (p a). subst.
    left; reflexivity.
    right; congruence.
    right; congruence.
  - apply ident_eq_dec; apply string_dec.
  - generalize dependent l0. induction X; destruct l0.
    left; reflexivity.
    right; congruence.
    right; congruence.
    destruct (IHX l0).
    destruct (p a). subst.
    left; reflexivity.
    right; congruence.
    right. congruence.
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
  - destruct (IHe0 e1); tryl; tryr.
  - generalize dependent l0.
    induction X; destruct l0; destruct (IHe0 e1); tryl; tryr.
    destruct x. destruct p0.
    simpl in *. destruct (p e3).
    destruct (pat_eq_dec p1 p0).
    destruct (IHX l0).
    tryl.
    tryr.
    tryr.
    tryr.
  - destruct (lit_eq_dec l l0); tryl; tryr.
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
  - destruct (IHe0_1 e1_1); tryr.
    destruct (IHe0_2 e1_2); tryr.
    destruct (lop_eq_dec lo l); tryl; tryr.
  - destruct (IHe0_1 e1_1).
    destruct (IHe0_2 e1_2).
    destruct (IHe0_3 e1_3).
    subst. tryl.
    tryr.
    tryr.
    tryr.
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
  - destruct (option_eq_dec _ string_dec o o0); tryr.
    destruct (IHe0_1 e1_1); tryr.
    destruct (IHe0_2 e1_2); tryl; tryr.
  - destruct (IHe0 e1); tryr.
    generalize dependent l. induction X; intro l0; destruct l0; tryl; tryr.
    destruct x. destruct p1. destruct p0. destruct p0.
    simpl in p.
    destruct (IHX l0); tryr.
    destruct (string_dec v v1); tryr.
    destruct (string_dec v0 v2); tryr.
    destruct (p e3); tryl; tryr.
  - destruct (locs_eq_dec l l0); tryr.
    destruct (IHe0 e1); tryr.
    subst; tryl.
Defined.
Hint Resolve exp_eq_dec : DecidableEquality.
Instance EqDec_exp : EqDec exp := exp_eq_dec.

Theorem dec_eq_dec : forall (d0 d1 : dec), {d0 = d1} + {d0 <> d1}.
Proof.
  decide equality; try (auto with DecidableEquality).
  - generalize dependent l. induction X; intros l'; destruct l'.
    left; reflexivity.
    right; congruence.
    right; congruence.
    destruct (IHX l').
    destruct (p d).
    subst; left; reflexivity.
    right; congruence.
    right; congruence.
  - generalize dependent l0. induction X0; intros l'; destruct l'.
    left; reflexivity.
    right; congruence.
    right; congruence.
    destruct (IHX0 l').
    destruct (p d).
    subst; left; reflexivity.
    right; congruence.
    right; congruence.
  - generalize dependent l. induction X; intros l'; destruct l'.
    left; reflexivity.
    right; congruence.
    right; congruence.
    destruct (IHX l').
    destruct (p d).
    subst; left; reflexivity.
    right; congruence.
    right; congruence.
Defined.
Hint Resolve dec_eq_dec : DecidableEquality.

(*-------------------------------------------------------------------*)
