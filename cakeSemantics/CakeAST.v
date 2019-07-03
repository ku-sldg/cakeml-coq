Require Import List.
Import ListNotations.
Require Import BinNums.
Require Import String.
Require Import ZArith.BinInt.

Require Import CakeSem.Namespace.
Require Import CakeSem.Utils.

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
  | Addw : opw.
  (* | Subw : opw. *)

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

Inductive op : Type :=
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

Inductive lop : Type :=
  | And : lop
  | Or : lop.

(* Inductive Forall' (A : Type) (P' : A -> Set) : list A -> Set := *)
(* | Forall_nil' : Forall' A P' [] *)
(* | Forall_cons' : forall (x : A) (l : list A), P' x -> Forall' A P' l -> Forall' A P' (x :: l). *)

(* LATER: replace using LibList function *)

(* Helper relation for lists *)
Inductive Forall'' (A : Type) (P'' : A -> Type) : list A -> Type :=
| Forall_nil'' : Forall'' A P'' []
| Forall_cons'' : forall (x : A) (l : list A), P'' x -> Forall'' A P'' l -> Forall'' A P'' (x :: l).

(* We need to build our own inductive principles for a bit *)
Unset Elimination Schemes.
(* Set Elimination Schemes. *)
(* Patterns *)

(* Types *)

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
  | Ptannot : pat -> ast_t -> pat.

(* locs Defined elsewhere in the Lem spec *)
Definition locs : Type := nat.

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


(** BACKPORT the new definition without accumulator

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

*)

Fixpoint pat_bindings (p : pat) : list varN :=
  match p with
  | Pany => []
  | Pvar n => n :: []
  | Plit l => []
  | Pcon _ ps => List.fold_right (fun p acc => acc ++ pat_bindings p) [] ps
  | Pref p => pat_bindings p
  | Ptannot p _ => pat_bindings p
  end.


(*-------------------------------------------------------------------*)
(** Begin induction principle *)

(* LATER: could use List.fold_right function *)

(** AST *)

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


(** PAT *)

Fixpoint pat_rect (P : pat -> Type)
         (H1 : P Pany)
         (H2 : forall (v : varN), P (Pvar v))
         (H3 : forall (l : lit), P (Plit l))
         (H4 : forall (o : constr_id) (l : list pat), Forall'' pat P l -> P (Pcon o l))
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

(* LATER: above could use List.fold_right function *)

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
         (H1 : forall (e : exp), P e -> P (ERaise e))
         (H2 : forall (e : exp), P e -> forall (l : list (pat * exp)), Forall'' (pat * exp) (exp_rect_helper P) l
                                                            -> P (EHandle e l))
         (H3 : forall (l : lit), P (ELit l))
         (H4 : forall (o : constr_id) (l : list exp), Forall'' exp P l
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


(** DEC *)

Fixpoint dec_rect (P : dec -> Type)
         (H1 : forall (l : locs) (p : pat) (e : exp), P (Dlet l p e))
         (H2 : forall (l : locs) (lv : list (varN * varN * exp)), P (Dletrec l lv))
         (H3 : forall (l : locs) (t : typeDef), P (Dtype l t))
         (H4 : forall (l : locs) (lt : list tvarN) (t : typeN) (a : ast_t), P (Dtabbrev l lt t a))
         (H5 : forall (l : locs) (c : conN) (la : list ast_t), P (Dexn l c la))
         (H6 : forall (m : modN) (l : list dec), Forall'' dec P l -> P (Dmod m l))
         (H7 : forall (l0 : list dec) (l1 : list dec), Forall'' dec P l0 -> Forall'' dec P l1 -> P (Dlocal l0 l1))
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
                   | h::t => Forall_cons'' dec P h t (dec_rect P H1 H2 H3 H4 H5 H6 H7 h) (loop t)
                   end
               in
               H6 m l (loop l)
  | Dlocal l0 l1 => let fix loop (l : list dec) :=
                       match l with
                       | [] => Forall_nil'' dec P
                       | h::t => Forall_cons'' dec P h t (dec_rect P H1 H2 H3 H4 H5 H6 H7 h) (loop t)
                       end
                   in
               H7 l0 l1 (loop l0) (loop l1)
  end.

Definition dec_rec (P : dec -> Set) := dec_rect P.
Definition dec_ind (P : dec -> Prop) := dec_rect P.


(** End induction principle *)
(*-------------------------------------------------------------------*)

