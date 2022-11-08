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
Scheme Equality for opn.

Inductive opb : Type :=
  | Lt : opb
  | Gt : opb
  | Leq : opb
  | Geq : opb.
Scheme Equality for opb.

Inductive opw : Type :=
  | Andw : opw
  | Orw : opw
  | Xorw : opw
  | Addw : opw
  | Subw : opw.
Scheme Equality for opw.

Inductive shift : Type :=
  | Lsl : shift
  | Lsr : shift
  | Asr : shift
  | Ror : shift.
Scheme Equality for shift.

Notation modN := string.
Notation varN := string.
Notation conN := string.
Notation typeN := string.
Notation tvarN := string.

Inductive word_size : Type :=
  | W8 : word_size
  | W64 : word_size.
Scheme Equality for word_size.

Inductive fpcmp : Type :=
| FP_Less | FP_LessEqual | FP_Greater | FP_GreaterEqual | FP_Equal.
Scheme Equality for fpcmp.

Inductive fpuop : Type :=
| FP_Abs | FP_Neg | FP_Sqrt.
Scheme Equality for fpuop.

Inductive fpbop : Type :=
| FP_Add | FP_Sub | FP_Mul | FP_Div.
Scheme Equality for fpbop.

Inductive fptop : Set :=
| FP_Fma.
Scheme Equality for fptop.

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
Scheme Equality for op.

Inductive lop : Type :=
  | And : lop
  | Or : lop.
Scheme Equality for lop.

(* Helper relation for lists *)
Inductive Forall'' (A : Type) (P'' : A -> Type) : list A -> Type :=
| Forall_nil'' : Forall'' A P'' []
| Forall_cons'' : forall (x : A) (l : list A), P'' x -> Forall'' A P'' l -> Forall'' A P'' (x :: l).

Arguments Forall'' {A } _.

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

Inductive pat : Type :=
| Pany : pat
| Pvar : varN -> pat
| Plit : lit -> pat
| Pcon : constr_id -> list pat -> pat
| Pref : pat -> pat
| Pas : pat -> varN -> pat
| Ptannot : pat -> ast_t -> pat.

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
  | ETannot : exp -> ast_t -> exp
  | ELannot : exp -> locs -> exp.

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

Fixpoint pat_bindings (p : pat) (already_bound : list varN) : list varN :=
  match p with
  | Pany => already_bound
  | Pvar n => n :: already_bound
  | Plit _ => already_bound
  | Pcon _ ps => List.fold_right (fun p acc => acc ++ pat_bindings p already_bound) [] ps
  | Pref p' => pat_bindings p' already_bound ++ already_bound
  | Pas p' n => pat_bindings p' (n :: already_bound)
  | Ptannot p' _ => pat_bindings p' already_bound
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
  (H0 : P Pany)
  (H1 : forall (v : varN), P (Pvar v))
  (H2 : forall (l : lit), P (Plit l))
  (H3 : forall (o : constr_id) (l : list pat), Forall'' P l -> P (Pcon o l))
  (H4 : forall (p : pat), P p -> P (Pref p))
  (H5 : forall (p : pat) (n : varN), P p -> P (Pas p n))
  (H6 : forall (p : pat) (a : ast_t), P p -> P (Ptannot p a))
  (p : pat) : P p :=
  let pat_rect'' := pat_rect' P H0 H1 H2 H3 H4 H5 H6 in
  match p return (P p) with
  | Pany => H0
  | Pvar v => H1 v
  | Plit l => H2 l
  | Pcon o l => let fix loop (l : list pat) :=
                   match l with
                   | [] => Forall_nil'' pat P
                   | h::t => Forall_cons'' pat P h t (pat_rect'' h) (loop t)
                   end
               in
               H3 o l (loop l)
  | Pref p' => H4 p' (pat_rect'' p')
  | Pas p' n => H5 p' n (pat_rect'' p')
  | Ptannot p' a => H6 p' a (pat_rect'' p')
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
         (H11 : forall (e : exp) (a : ast_t), P e -> P (ETannot e a))
         (H12 : forall (e : exp) (l : locs), P e -> P (ELannot e l))
         (e : exp) : P e :=
  let exp_rect' := fun e' => exp_rect' P H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 e' in
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
  | ETannot e' a  => H11 e' a (exp_rect' e')
  | ELannot e' l  => H12 e' l (exp_rect' e')
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

(** Begin boolean equality *)
(*-------------------------------------------------------------------*)

Scheme Equality for list.
Scheme Equality for ident.
Scheme Equality for option.
Scheme Equality for prod.

Definition lit_beq (lit1 lit2 : lit) : bool :=
  match lit1, lit2 with
  | IntLit i1, IntLit i2 => Z.eqb i1 i2
  | CharLit c1, CharLit c2 => Ascii.eqb c1 c2
  | StrLit s1, StrLit s2 => String.eqb s1 s2
  | Word8Lit w1, Word8Lit w2 => word_equality 8 w1 w2
  | Word64Lit w1, Word64Lit w2 => word_equality 64 w1 w2
  | _, _ => false
  end.

Fixpoint ast_t_beq (a1 a2 : ast_t) : bool :=
  match a1, a2 with
  | Atvar v1, Atvar v2 => String.eqb v1 v2
  | Atfun a3 a4, Atfun a5 a6 => andb (ast_t_beq a3 a5) (ast_t_beq a4 a6)
  | Attup l1, Attup l2 => list_beq _ ast_t_beq l1 l2
  | Atapp l1 i1, Atapp l2 i2 => andb (list_beq _ ast_t_beq l1 l2)
                                    (ident_beq _ _ String.eqb String.eqb i1 i2)
  | _, _ => false
  end.

Definition constr_id_beq := option_beq _ (ident_beq _ _ String.eqb String.eqb).

Fixpoint pat_beq (p1 p2 : pat) :=
  match p1, p2 with
  | Pvar s1, Pvar s2 => String.eqb s1 s2
  | Pcon cid1 l1, Pcon cid2 l2 => andb (constr_id_beq cid1 cid2) (list_beq _ pat_beq l1 l2)
  | _, _ => false
  end.

Arguments list_beq {_}.
Arguments prod_beq {_} {_}.

Fixpoint exp_beq (exp1 exp2 : exp) :=
  match exp1, exp2 with
  | ERaise e1, ERaise e2 => exp_beq e1 e2
  | EHandle e1 l1, EHandle e2 l2 => andb (exp_beq e1 e2) (list_beq (prod_beq pat_beq exp_beq) l1 l2)
  | ELit lit1, ELit lit2 => lit_beq lit1 lit2
  | ECon c1 l1, ECon c2 l2 => andb (constr_id_beq c1 c2) (list_beq exp_beq l1 l2)
  | EVar i1, EVar i2 => ident_beq _ _ String.eqb String.eqb i1 i2
  | EFun v1 e1, EFun v2 e2 => andb (String.eqb v1 v2) (exp_beq e1 e2)
  | EApp o1 l1, EApp o2 l2 => andb (op_beq o1 o2) (list_beq exp_beq l1 l2)
  | ELog lo1 e1 e2, ELog lo2 e3 e4 => andb (andb (lop_beq lo1 lo2) (exp_beq e1 e3)) (exp_beq e2 e4)
  | EIf c1 t1 e1, EIf c2 t2 e2 => andb (andb (exp_beq c1 c2) (exp_beq t1 t2)) (exp_beq e1 e2)
  | EMat e1 l1, EMat e2 l2 => andb (exp_beq e1 e2) (list_beq (prod_beq pat_beq exp_beq) l1 l2)
  | ELet o1 e1 e2, ELet o2 e3 e4 => andb (andb (option_beq _ String.eqb o1 o2) (exp_beq e1 e3))
                                        (exp_beq e2 e4)
  | ELetrec l1 e1, ELetrec l2 e2 => andb (list_beq (prod_beq
                                                            (prod_beq String.eqb String.eqb)
                                                            exp_beq) l1 l2)
                                        (exp_beq e1 e2)
  | ELannot e1 lc1, ELannot e2 lc2 => andb (exp_beq e1 e2) (list_beq  Nat.eqb lc1 lc2)
  | _, _ => false
  end.


Definition typeDef_beq := list_beq (prod_beq (prod_beq (list_beq String.eqb) String.eqb) (list_beq (prod_beq String.eqb (list_beq ast_t_beq)))).

Open Scope bool_scope.

Fixpoint dec_beq (dec1 dec2 : dec) :=
  match dec1, dec2 with
  | Dlet l1 p1 e1, Dlet l2 p2 e2 => list_beq Nat.eqb l1 l2 && pat_beq p1 p2 && exp_beq e1 e2
  | Dletrec l1 lvve1 , Dletrec l2 lvve2 => list_beq Nat.eqb l1 l2 &&
                                            list_beq (prod_beq (prod_beq String.eqb String.eqb) exp_beq) lvve1 lvve2
  | Dtype l1 t1, Dtype l2 t2 => list_beq Nat.eqb l1 l2 && typeDef_beq t1 t2
  | Dtabbrev l1 lts1 tn1 ast1 , Dtabbrev l2 lts2 tn2 ast2 => list_beq Nat.eqb l1 l2 &&
                                                              list_beq String.eqb lts1 lts2 &&
                                                              String.eqb tn1 tn2 &&
                                                              ast_t_beq ast1 ast2
  | Dexn l1 cn1 last1, Dexn l2 cn2 last2 => list_beq Nat.eqb l1 l2 &&
                                             String.eqb cn1 cn2 &&
                                             list_beq ast_t_beq last1 last2
  | Dmod mn1 ld1, Dmod mn2 ld2 => String.eqb mn1 mn2 &&
                                   list_beq dec_beq ld1 ld2

  | Dlocal ld11 ld12, Dlocal ld21 ld22 => list_beq dec_beq ld11 ld21 &&
                                           list_beq dec_beq ld12 ld22
  | _, _ => false
  end.

(** End boolean equality *)
(*-------------------------------------------------------------------*)

(** Decidable Equality for terms, patterns, and expressions *)
(*-------------------------------------------------------------------*)

Theorem lit_eq_dec (l l' : lit) : {l = l'} + {l <> l'}.
  decide equality; auto with DecidableEquality. apply (word_eq_dec 8). apply (word_eq_dec 64). Defined.
#[export] Hint Resolve lit_eq_dec : DecidableEquality.

(* Theorem opn_eq_dec (o o' : opn) : {o = o'} + {o <> o'}. *)
(*  decide equality. Defined. *)
#[export] Hint Resolve opn_eq_dec : DecidableEquality.

(* Theorem opb_eq_dec (o o' : opn) : {o = o'} + {o <> o'}. *)
(*   decide equality. *)
(* Defined. *)
#[export] Hint Resolve opb_eq_dec : DecidableEquality.

(* Theorem opw_eq_dec (o o' : opn) : {o = o'} + {o <> o'}. *)
(*   decide equality. *)
(* Defined. *)
#[export] Hint Resolve opw_eq_dec : DecidableEquality.

(* Theorem shift_eq_dec (o o' : opn) : {o = o'} + {o <> o'}. *)
(*   decide equality. *)
(* Defined. *)
#[export] Hint Resolve shift_eq_dec : DecidableEquality.

(* Theorem op_eq_dec : forall (o0 o1 : op), {o0 = o1} + {o0 <> o1}. *)
(* Proof. *)
(*   decide equality; try (apply string_dec); decide equality. *)
(* Defined. *)
#[export] Hint Resolve op_eq_dec : DecidableEquality.

(* Theorem lop_eq_dec : forall (l0 l1 : lop), {l0 = l1} + {l0 <> l1}. *)
(* Proof. decide equality.  Defined. *)
#[export] Hint Resolve lop_eq_dec : DecidableEquality.

Theorem ast_t_eq_dec : forall (a1 a2 : ast_t), {a1 = a2} + {a1 <> a2}.
Proof.
  decide equality;
    auto with DecidableEquality.
  - generalize dependent l0; induction H; destruct l0.
    left; reflexivity.
    right; congruence.
    right; congruence.
    destruct (IHForall'' l0). destruct (p a). subst.
    left; reflexivity.
    right; congruence.
    right; congruence.
  - generalize dependent l0. induction H; destruct l0.
    left; reflexivity.
    right; congruence.
    right; congruence.
    destruct (IHForall'' l0).
    destruct (p a). subst.
    left; reflexivity.
    right; congruence.
    right. congruence.
Defined.
#[export] Hint Resolve ast_t_eq_dec : DecidableEquality.

Theorem constr_id_eq_dec : forall (c0 c1 : constr_id), {c0 = c1} + {c0 <> c1}.
Proof.
  decide equality. auto with DecidableEquality.  Defined.
#[export] Hint Resolve constr_id_eq_dec : DecidableEquality.

Theorem pat_eq_dec : forall (p0 p1 : pat), {p0 = p1} + {p0 <> p1}.
Proof.
  decide equality; auto with DecidableEquality.
  generalize dependent l0;
  induction X; destruct l0; try (right; congruence); try (left; reflexivity).
  destruct (IHX l0); destruct (p p2); subst; try (left; reflexivity); try (right; congruence).
Defined.
#[export] Hint Resolve pat_eq_dec : DecidableEquality.

Theorem typeDef_eq_dec : forall (t0 t1 : typeDef), {t0 = t1} + {t0 <> t1}.
Proof. decide equality; auto with DecidableEquality.  Defined.
#[export] Hint Resolve typeDef_eq_dec : DecidableEquality.

Theorem locs_eq_dec : forall (l0 l1 : locs), {l0 = l1} + {l0 <> l1}.
Proof.
  decide equality; auto with DecidableEquality.
Defined.
#[export] Hint Resolve locs_eq_dec : DecidableEquality.
