Require Import List.
Import ListNotations.
Require Import BinNums.
Require Import String.
Require Import ZArith.BinInt.

Require Import CakeSem.Namespace.
Require Import CakeSem.Utils.
Require Import CakeSem.Word.

Create HintDb DecidableEquality.
Hint Resolve string_dec : DecidableEquality.
Hint Resolve Ascii.ascii_dec : DecidableEquality.
Hint Resolve (word_eq_dec 8) : DecidableEquality.
Hint Resolve (word_eq_dec 64) : DecidableEquality.
Hint Resolve Z.eq_dec : DecidableEquality.
Hint Resolve list_eq_dec : DecidableEquality.
Hint Resolve Peano_dec.eq_nat_dec : DecidableEquality.

(* Literal constants *)
Inductive lit : Set :=
| IntLit : int -> lit
| CharLit : char -> lit
| StrLit : string -> lit
| Word8Lit : word8 -> lit
| Word64Lit : word64 -> lit.

Theorem lit_eq_dec (l l' : lit) : {l = l'} + {l <> l'}.
  decide equality; auto with DecidableEquality.  Qed.
Hint Resolve lit_eq_dec : DecidableEquality.

Inductive opn : Set :=
| Plus : opn
| Minus : opn
| Times : opn
| Divide : opn
| Modulo : opn.

Theorem opn_eq_dec (o o' : opn) : {o = o'} + {o <> o'}.
 decide equality. Qed.
Hint Resolve opn_eq_dec : DecidableEquality.

Inductive opb : Set :=
| Lt : opb
| Gt : opb
| Leq : opb
| Geq : opb.

Theorem opb_eq_dec (o o' : opn) : {o = o'} + {o <> o'}.
  decide equality.
Qed.
Hint Resolve opb_eq_dec : DecidableEquality.

Inductive opw : Set :=
| Andw : opw
| Orw : opw
| Xorw : opw
| Addw : opw.
(* | Subw : opw. *)

Theorem opw_eq_dec (o o' : opn) : {o = o'} + {o <> o'}.
  decide equality.
Qed.
Hint Resolve opw_eq_dec : DecidableEquality.

Inductive shift : Set :=
| Lsl : shift
| Lsr : shift
| Asr : shift
| Ror : shift.

Theorem shift_eq_dec (o o' : opn) : {o = o'} + {o <> o'}.
  decide equality.
Qed.
Hint Resolve shift_eq_dec : DecidableEquality.

Definition modN := string.

Definition varN := string.

Definition conN := string.

Definition typeN := string.

Definition tvarN := string.

Inductive word_size : Set :=
| W8 : word_size
| W64 : word_size.

Inductive op : Set :=
| Opn : opn -> op
| Opb : opb -> op
| Opw : word_size -> opw -> op
| Shift : word_size -> shift -> nat -> op
| Equality : op
(* Floating point currently d.n.e *)
(* | OpFpCmp *)
(* | OpFpUmp *)
(* | OpFpBmp *)
| Opapp : op
| Opassign : op
| Opref : op
| Opderef : op
| Aw8alloc : op
| Aw8sub : op
| Aw8length : op
| Aw8update : op
| WordFromInt : word_size -> op
| WordToInt : word_size -> op
| CopyStrStr : op
| CopyStrAw8 : op
| CopyAw8Str : op
| CopyAw8Aw8 : op
| Ord : op
| Chr : op
| Chopb : opb -> op
| Implode : op
| Strsub : op
| Strlen : op
| Strcat : op
| VfromList : op
| Vsub : op
| Vlength : op
| Aalloc : op
| AallocEmpty : op
| Asub : op
| Alength : op
| Aupdate : op
| ListAppend : op
| ConfigGC : op
| FFI : string -> op.

Theorem op_eq_dec : forall (o0 o1 : op), {o0 = o1} + {o0 <> o1}.
Proof. repeat decide equality.  Qed.
Hint Resolve op_eq_dec : DecidableEquality.

Inductive lop : Set :=
| And : lop
| Or : lop.

Theorem lop_eq_dec : forall (l0 l1 : lop), {l0 = l1} + {l0 <> l1}.
Proof. decide equality.  Qed.
Hint Resolve lop_eq_dec : DecidableEquality.

(* Inductive Forall' (A : Set) (P' : A -> Set) : list A -> Set := *)
(* | Forall_nil' : Forall' A P' [] *)
(* | Forall_cons' : forall (x : A) (l : list A), P' x -> Forall' A P' l -> Forall' A P' (x :: l). *)

(* Helper relation for lists *)
Inductive Forall'' (A : Type) (P'' : A -> Type) : list A -> Type :=
| Forall_nil'' : Forall'' A P'' []
| Forall_cons'' : forall (x : A) (l : list A), P'' x -> Forall'' A P'' l -> Forall'' A P'' (x :: l).

(* We need to build our own inductive principles for a bit *)
Unset Elimination Schemes.

(* Types *)
Inductive ast_t : Set :=
| Atvar : tvarN -> ast_t
| Atfun : ast_t -> ast_t -> ast_t
| Attup : list ast_t -> ast_t
| Atapp : list ast_t -> ident modN typeN -> ast_t.


Fixpoint ast_t_rect (P : ast_t -> Type)
         (H1 : forall (t : tvarN), P (Atvar t))
         (H2 : forall (a1 a2 : ast_t), P a1 -> P a2 -> P (Atfun a1 a2))
         (H3 : forall (l : list ast_t), Forall'' ast_t P l -> P (Attup l))
         (H4 : forall (l : list ast_t) (i : ident modN typeN), Forall'' ast_t P l -> P (Atapp l i))
         (a : ast_t) : P a :=
  match a with
  | Atvar t => H1 t
  | Atfun a1 a2 => H2 a1 a2 (ast_t_rect P H1 H2 H3 H4 a1) (ast_t_rect P H1 H2 H3 H4 a2)
  | Attup l => let fix F (ls : list ast_t) :=
                   match ls with
                   | [] => Forall_nil'' ast_t P
                   | h::t => Forall_cons'' ast_t P h t (ast_t_rect P H1 H2 H3 H4 h) (F t)
                   end
               in H3 l (F l)
  | Atapp l i => let fix F (ls : list ast_t) :=
                   match ls with
                   | [] => Forall_nil'' ast_t P
                   | h::t => Forall_cons'' ast_t P h t (ast_t_rect P H1 H2 H3 H4 h) (F t)
                   end
               in H4 l i (F l)
  end.

Definition ast_t_ind (P : ast_t -> Prop) := ast_t_rect P.
Definition ast_t_rec (P : ast_t -> Set) := ast_t_rect P.

Theorem ast_t_eq_dec : forall (a1 a2 : ast_t), {a1 = a2} + {a1 <> a2}.
Proof.
  decide equality; auto with DecidableEquality; try (apply ident_eq_dec; apply string_dec);
  generalize dependent l0;
  induction H; destruct l0;
    try (left; reflexivity);
    try (right; discriminate);
    try (destruct (p a);
         destruct (IHForall'' l0);
         try (inversion e0);
         try (right; intro con; injection con; contradiction);
         rewrite e; left; reflexivity).
Qed.
Hint Resolve ast_t_eq_dec : DecidableEquality.

(* Set Elimination Schemes. *)
(* Patterns *)

Inductive pat : Set :=
| Pany : pat
| Pvar : varN -> pat
| Plit : lit -> pat
| Pcon : option (ident modN conN) -> list pat -> pat
| Pref : pat -> pat
| Ptannot : pat -> ast_t -> pat.

Fixpoint pat_rect (P : pat -> Type)
         (H1 : P Pany)
         (H2 : forall (v : varN), P (Pvar v))
         (H3 : forall (l : lit), P (Plit l))
         (H4 : forall (o : option (ident modN conN)) (l : list pat), Forall'' pat P l -> P (Pcon o l))
         (H5 : forall (p : pat), P p -> P (Pref p))
         (H6 : forall (p : pat), P p -> forall (a : ast_t), P (Ptannot p a))
         (p : pat) : P p :=
  match p return (P p) with
  | Pany => H1
  | Pvar v => H2 v
  | Plit l => H3 l
  | Pcon o l => let fix loop (l : list pat) :=
                   match l with
                   | [] => Forall_nil'' pat P
                   | h::t => Forall_cons'' pat P h t (pat_rect P H1 H2 H3 H4 H5 H6 h) (loop t)
                   end
               in
               H4 o l (loop l)
  | Pref p'  => H5 p' (pat_rect P H1 H2 H3 H4 H5 H6 p')
  | Ptannot p' a => H6 p' (pat_rect P H1 H2 H3 H4 H5 H6 p') a
  end.

Definition pat_rec (P : pat -> Set) := pat_rect P.
Definition pat_ind (P : pat -> Prop) := pat_rect P.

Theorem pat_eq_dec : forall (p0 p1 : pat), {p0 = p1} + {p0 <> p1}.
Proof. decide equality; auto with DecidableEquality.
       generalize dependent l0.
         induction l; destruct l0; try (left; reflexivity); try (right; discriminate).
       inversion H.
       destruct (H2 p). rewrite e.
       destruct (IHl H3 l0).
       rewrite e0; left; reflexivity.
       right; intro con; inversion con; auto.
       right; intro con; inversion con; auto.
       decide equality. apply ident_eq_dec; apply string_dec.
Qed.
Hint Resolve pat_eq_dec : DecidableEquality.
Set Elimination Schemes.
(* locs Defined elsewhere in the Lem spec *)
Definition locs := nat.

Unset Elimination Schemes.
(* Expressions *)
Inductive exp : Set :=
| ERaise : exp -> exp
| EHandle : exp -> list (pat * exp) -> exp
| ELit : lit -> exp
| ECon : option (ident modN conN) -> list exp -> exp
| EVar : ident modN varN -> exp
| EFun : varN -> exp -> exp
| EApp : op -> list exp -> exp
| ELog : lop -> exp -> exp -> exp
| EIf  : exp -> exp -> exp -> exp
| EMat : exp -> list (pat * exp) -> exp
| ELet : option varN -> exp -> exp -> exp
| ELetrec : list (varN * varN * exp) -> exp -> exp
| ETannot : exp -> ast_t -> exp
| ELannot : exp -> locs -> exp.

Definition exp_rect_helper (P : exp -> Type) (p : pat * exp) : Type :=
  match p with
  | (x, y) => P y
  end.

Definition exp_rect_helper' (P : exp -> Type) (p : varN * varN * exp) : Type :=
  match p with
  | (x, y, z) => P z
  end.

Fixpoint exp_rect (P : exp -> Type)
         (H1 : forall (e : exp), P e -> P (ERaise e))
         (H2 : forall (e : exp), P e -> forall (l : list (pat * exp)), Forall'' (pat * exp) (exp_rect_helper P) l
                                                            -> P (EHandle e l))
         (H3 : forall (l : lit), P (ELit l))
         (H4 : forall (o : option (ident modN conN)) (l : list exp), Forall'' exp P l
                                                                -> P (ECon o l))
         (H5 : forall (i : ident modN varN), P (EVar i))
         (H6 : forall (v : varN) (e : exp), P e -> P (EFun v e))
         (H7 : forall (o : op) (l : list exp), Forall'' exp P l -> P (EApp o l))
         (H8 : forall (l : lop) (e1 e2 : exp), P e1 -> P e2 -> P (ELog l e1 e2))
         (H9 : forall (e1 e2 e3 : exp), P e1 -> P e2 -> P e3 -> P (EIf e1 e2 e3))
         (H10 : forall (e : exp), P e -> forall (l : list (pat * exp)), Forall'' (pat * exp) (exp_rect_helper P) l
                                                             -> P (EMat e l))
         (H11 : forall (o : option varN) (e1 e2 : exp), P e1 -> P e2 -> P (ELet o e1 e2))
         (H12 : forall (l : list (varN * varN * exp)), Forall'' (varN * varN * exp) (exp_rect_helper' P) l
                                                  -> forall (e : exp), P e -> P (ELetrec l e))
         (H13 : forall (e : exp) (a : ast_t), P e -> P (ETannot e a))
         (H14 : forall (e : exp) (l : locs), P e -> P (ELannot e l))
         (e : exp) : P e :=
  let exp_rect' := fun e' => exp_rect P H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 e' in
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
  | ERaise e' => H1 e' (exp_rect' e')
  | EHandle e' l => H2 e' (exp_rect' e') l (pair_loop l)
  | ELit l    => H3 l
  | ECon o l  => H4 o l (loop l)
  | EVar i    => H5 i
  | EFun v e' => H6 v e' (exp_rect' e')
  | EApp o l  => H7 o l (loop l)
  | ELog l e1 e2 => H8 l e1 e2 (exp_rect' e1) (exp_rect' e2)
  | EIf  e1 e2 e3 => H9 e1 e2 e3 (exp_rect' e1) (exp_rect' e2) (exp_rect' e3)
  | EMat e' l     => H10 e' (exp_rect' e') l (pair_loop l)
  | ELet o e1 e2  => H11 o e1 e2 (exp_rect' e1) (exp_rect' e2)
  | ELetrec l e'  => H12 l (trip_loop l) e' (exp_rect' e')
  | ETannot e' a  => H13 e' a (exp_rect' e')
  | ELannot e' l  => H14 e' l (exp_rect' e')
  end.

Definition exp_rec (P : exp -> Set) := exp_rect P.
Definition exp_ind (P : exp -> Prop) := exp_rect P.

Theorem exp_eq_dec : forall (e0 e1 : exp), {e0 = e1} + {e0 <> e1}.
Proof.
  decide equality; auto with DecidableEquality;
    try (decide equality; try (apply ident_eq_dec); apply string_dec).

  generalize dependent l0.
  induction X; destruct l0; try (left; reflexivity); try (right; discriminate).
  assert ({x = p0} + {x <> p0}). {
    destruct x; destruct p0.
    simpl in p.
    destruct (p e4); destruct (pat_eq_dec p1 p0).
    rewrite e5. rewrite e6. left; reflexivity.
    right; intro con; inversion con; auto.
    right; intro con; inversion con; auto.
    right; intro con; inversion con; auto.
  }
  inversion H0. rewrite H1.
  destruct (IHX l0).
  rewrite e3. left; reflexivity.
  right; intro con; inversion con; auto.
  right; intro con; inversion con; auto.

  generalize dependent l0.
  induction H; destruct l0; try (left; reflexivity); try (right; discriminate).
  destruct (p e); destruct (IHForall'' l0).
  rewrite e3. rewrite e2. left; reflexivity.
  right; intro con; inversion con; auto.
  right; intro con; inversion con; auto.
  right; intro con; inversion con; auto.

  generalize dependent l0.
  induction H; destruct l0; try (left; reflexivity); try (right; discriminate).
  destruct (p e); destruct (IHForall'' l0).
  rewrite e3. rewrite e2. left; reflexivity.
  right; intro con; inversion con; auto.
  right; intro con; inversion con; auto.
  right; intro con; inversion con; auto.

  generalize dependent l0.
  induction X; destruct l0; try (left; reflexivity); try (right; discriminate).
  assert ({x = p0} + {x <> p0}). {
    destruct x; destruct p0.
    simpl in p.
    destruct (p e4); destruct (pat_eq_dec p1 p0).
    rewrite e5. rewrite e6. left; reflexivity.
    right; intro con; inversion con; auto.
    right; intro con; inversion con; auto.
    right; intro con; inversion con; auto.
  }
  inversion H0. rewrite H1.
  destruct (IHX l0).
  rewrite e3. left; reflexivity.
  right; intro con; inversion con; auto.
  right; intro con; inversion con; auto.


  generalize dependent l0.
  induction X; destruct l0.
  left; reflexivity.
  right; discriminate.
  right; discriminate.
  assert ({x = p0} + {x <> p0}). {
    destruct x; destruct p0; destruct p1; destruct p0.
    simpl in p.
    destruct (p e4); destruct (string_dec v v1); destruct (string_dec v0 v2);
    try (rewrite e5; rewrite e6; rewrite e7; left; reflexivity);
    try (right; intro con; inversion con; auto).
  }
  destruct H0; destruct (IHX l0); try (rewrite e3, e4; left; reflexivity);
                                  try (right; intro con; inversion con; auto).
Qed.

Hint Resolve exp_eq_dec : DecidableEquality.

Definition typeDef := list (list tvarN * typeN * list (conN * list ast_t)).
Theorem typeDef_eq_dec : forall (t0 t1 : typeDef), {t0 = t1} + {t0 <> t1}.
Proof. decide equality. decide equality.
       apply list_eq_dec; decide equality; auto with DecidableEquality.
       decide equality; auto with DecidableEquality.  Qed.
Hint Resolve typeDef_eq_dec : DecidableEquality.

(* Declarations *)
Inductive dec : Set :=
| Dlet : locs -> pat -> exp -> dec
| Dletrec : locs -> list (varN * varN * exp) -> dec
| Dtype : locs -> typeDef -> dec
| Dtabbrev : locs -> list tvarN -> typeN -> ast_t -> dec
| Dexn : locs -> conN -> list ast_t -> dec
| Dmod : modN -> list dec -> dec.

Fixpoint dec_rect (P : dec -> Type)
         (H1 : forall (l : locs) (p : pat) (e : exp), P (Dlet l p e))
         (H2 : forall (l : locs) (lv : list (varN * varN * exp)), P (Dletrec l lv))
         (H3 : forall (l : locs) (t : typeDef), P (Dtype l t))
         (H4 : forall (l : locs) (lt : list tvarN) (t : typeN) (a : ast_t), P (Dtabbrev l lt t a))
         (H5 : forall (l : locs) (c : conN) (la : list ast_t), P (Dexn l c la))
         (H6 : forall (m : modN) (l : list dec), Forall'' dec P l -> P (Dmod m l))
         (d : dec) : P d :=
  match d with
  | Dlet l p e => H1 l p e
  | Dletrec l lv => H2 l lv
  | Dtype l t => H3 l t
  | Dtabbrev l lt t a => H4 l lt t a
  | Dexn l c la => H5 l c la
  | Dmod m l => let fix loop (l : list dec) :=
                   match l with
                   | [] => Forall_nil'' dec P
                   | h::t => Forall_cons'' dec P h t (dec_rect P H1 H2 H3 H4 H5 H6 h) (loop t)
                   end
               in
               H6 m l (loop l)
  end.

Definition dec_rec (P : dec -> Set) := dec_rect P.
Definition dec_ind (P : dec -> Prop) := dec_rect P.

Theorem dec_eq_dec : forall (d0 d1 : dec), {d0 = d1} + {d0 <> d1}.
Proof. decide equality; auto with DecidableEquality.
       apply list_eq_dec. decide equality; auto with DecidableEquality.
       decide equality; auto with DecidableEquality.
       generalize dependent l0.
       induction H; destruct l0;
         try (left; reflexivity); try (right; discriminate).
       destruct (p d); destruct (IHForall'' l0);
         try (rewrite e, e0; left; reflexivity);
         try (right; intro con; inversion con; auto).
Qed.
Hint Resolve dec_eq_dec : DecidableEquality.

Fixpoint pat_bindings (p : pat) (already_bound : list varN) : list varN :=
  let fix pats_bindings (ps : list pat) (already_bound : list varN) : list varN :=
      match ps with
      | [] => already_bound
      | p::ps => pats_bindings ps (pat_bindings p already_bound)
      end
  in
  match p with
  | Pany => already_bound
  | Pvar n => n :: already_bound
  | Plit l => already_bound
  | Pcon _ ps => pats_bindings ps already_bound
  | Pref p => pat_bindings p already_bound
  | Ptannot p _ => pat_bindings p already_bound
  end.
