Set Implicit Arguments.

Require Import Arith.
Require Import Ascii.
Import Bool.Sumbool.
Require Import List.
Import ListNotations.

(* Require Import Strings.Ascii. *)
Require Import ZArith.
Require ZArith.Zdigits.

Require Import CakeSem.ffi.FFI.
Require Import CakeSem.Utils.
Require Import CakeSem.Namespace.
Require Import CakeSem.CakeAST.
Require Import CakeSem.FreeVars.

Open Scope string_scope.
Open Scope list_scope.

(** LATER: throughout the files, every definition should have all its arguments
    and its return type explicit. This helps a lot reading the specification. *)

(* ********************************************************************** *)
(** * Auxiliary semantics constructs *)

(* ---------------------------------------------------------------------- *)
(** ** Stamps and predefined constructors *)

Inductive stamp : Type :=
  | TypeStamp : conN -> nat -> stamp
  | ExnStamp : nat -> stamp.

Theorem stamp_eq_dec : forall (s0 s1 : stamp), {s0 = s1} + {s0 <> s1}.
Proof.
  decide equality; auto with DecidableEquality.
Defined.
Hint Resolve stamp_eq_dec : DecidableEquality.
(* LATER : add type annotations? *)

Definition bind_stamp := ExnStamp 0.
Definition chr_stamp := ExnStamp 1.
Definition div_stamp := ExnStamp 2.
Definition subscript_stamp := ExnStamp 3.

(* BACKPORT: bind_exn_v is used to mean "match failure", but that's not an intuitive name for it *)

(* ---------------------------------------------------------------------- *)
(** ** Environments *)

(* BACKPORT: use of this abbreviations in the definition of sem_env *)
Definition env_ctor := namespace modN conN (nat * stamp).

(* QUESTION: what is the interest of being generic in the type of values? *)

Record sem_env (V : Type) := {
  sev : namespace modN varN V;
  sec : env_ctor }.

Arguments sev {V} _.
Arguments sec {V} _.

(** Auxiliary definition to mimic [{ env with sev = .. }] *)
Definition update_sev V (e:sem_env V) (x:namespace modN varN V) :=
  {| sev := x; sec := sec e |}.

(** Auxiliary definition to mimic [{ env with sec = .. }] *)
Definition update_sec V (e:sem_env V) x :=
  {| sev := sev e; sec := x |}.

(* BACKPORT: use this definition in semantics *)
Definition empty_sem_env {V : Type} : sem_env V :=
  {| sev := nsEmpty; sec := nsEmpty |}.

(* BACKPORT: extend_dec_env should be used in definition of combine_dec_result *)
Definition extend_dec_env (V : Type) (new_env env : sem_env V) : sem_env V :=
  {| sev := nsAppend (sev new_env) (sev env);
     sec := nsAppend (sec new_env) (sec env)|}.

Fixpoint optimize_sem_env {V : Type} (env : sem_env V) (fvs : list (ident modN varN)) : sem_env V :=
  match fvs with
    | [] => {| sec := sec env; sev := nsEmpty |}
    | id::fvs' => let opt := optimize_sem_env env fvs' in
                match nsLookup (ident_eq_dec _ _ string_dec string_dec) id (sev env) with
                | None => opt
                | Some v => {| sec := sec opt; sev := (id,v)::(sev opt) |}
                end
  end.

(* ---------------------------------------------------------------------- *)
(** ** Values *)

Unset Elimination Schemes.

Inductive val : Type :=
  (* | Litv : lit -> val *)
  | Conv : option stamp -> list val -> val
  | Closure : sem_env val -> varN -> exp -> val
  | Recclosure : sem_env val -> list (varN * varN * exp) -> varN -> val
  (* | Loc : nat -> val *)
  (* | Vectorv : list val -> val. *).

Set Elimination Schemes.
Definition env_val := namespace modN varN val.

(** [is_closure v] captures whether [v] is a closure or a recursive closure. *)

Definition is_closure (v:val) : Prop :=
  match v with
  | Closure _ _ _ => True
  | Recclosure _ _ _ => True
  | _ => False
  end.



(* ---------------------------------------------------------------------- *)
(** ** Predefined exceptions and constructors  *)

Definition bind_exn_v := Conv (Some bind_stamp) [].
Definition chr_exn_v  := Conv (Some chr_stamp) [].
Definition div_exn_v  := Conv (Some div_stamp) [].
Definition sub_exn_v  := Conv (Some subscript_stamp) [].

Definition bool_type_num := 0%nat.
Definition list_type_num := 1%nat.

(* BACKPORT: define these 3 shorthands *)

Definition ConvTrue := Conv (Some (TypeStamp "True"  bool_type_num)) [].
Definition ConvFalse := Conv (Some (TypeStamp "False"  bool_type_num)) [].
Definition ConvUnit := Conv None [].

Definition Boolv (b : bool) : val :=
  if b then ConvTrue  else ConvFalse.

(* Definition Propv (P:Prop) : val := *)
(*   Boolv (isTrue P). *)

(* ---------------------------------------------------------------------- *)
(** ** Result of an evaluation *)

(* Result of evaluation *)

Inductive abort : Type :=
  | Rtype_error : abort
  | Rtimeout_error : abort
  | Rffi_error : final_event -> abort.

Inductive error_result (A : Type) : Type :=
  | Rraise : A -> error_result A
  | Rabort : abort -> error_result A.

Arguments Rraise {A}.
Arguments Rabort {A}.

Inductive result (A : Type) (B : Type) : Type :=
  | Rval : A -> result A B
  | Rerr : error_result B -> result A B.

Arguments Rval {A} {B}.
Arguments Rerr {A} {B}.


Definition combine_dec_result {A : Type} (env : sem_env val) (r : result (sem_env val) A) :
  result (sem_env val) A :=
  match r with
  | Rerr err => r
  | Rval env' =>  Rval (extend_dec_env env' env)
  end.

(* ---------------------------------------------------------------------- *)
(** ** Store *)

Inductive store_v (A : Type) : Type :=
  (* Reference *)
  | Refv : A -> store_v A
  (* Byte array *)
  | W8array : list word8 -> store_v A
  (* Value array *)
  | Varray : list A -> store_v A.

Arguments Refv {A}.
Arguments W8array {A}.
Arguments Varray {A}.

(* The nth item in the list is the value at location n *)

Definition store (A : Type) :=
  list (store_v A).


(* ---------------------------------------------------------------------- *)
(** ** State *)

Record state (A : Type) :=
  {
    clock : nat;
    refs : store val;
    ffi : ffi_state A;
    next_type_stamp : nat;
    next_exn_stamp : nat
  }.

Arguments clock {A} _.
Arguments refs {A} _.
Arguments ffi {A} _.
Arguments next_type_stamp {A} _.
Arguments next_exn_stamp {A} _.
Arguments refs {A} _.

Definition state_update_refs_and_ffi A (st:state A) refs' (ffi':ffi_state A) :=
   {| clock := clock st;
      refs := refs';
      ffi := ffi';
      next_type_stamp := next_type_stamp st ;
      next_exn_stamp := next_exn_stamp st |}.

(** Auxiliary definition to mimic [{ st with next_type_stamp = .. }] *)
Definition state_update_next_type_stamp A (st:state A) x :=
   {| clock := clock st;
      refs := refs st;
      ffi := ffi st;
      next_type_stamp := x ;
      next_exn_stamp := next_exn_stamp st |}.

(** Auxiliary definition to mimic [{ st with next_exn_stamp = .. }] *)
Definition state_update_next_exn_stamp A (st:state A) x :=
   {| clock := clock st;
      refs := refs st;
      ffi := ffi st;
      next_type_stamp := next_type_stamp st ;
      next_exn_stamp := x |}.


(* ---------------------------------------------------------------------- *)
(** ** Pattern-maching result *)

Inductive match_result (A : Type) : Type :=
  | No_match : match_result A
  | Match_type_error : match_result A
  | Match : A -> match_result A.

Arguments No_match {A}.
Arguments Match_type_error {A}.
Arguments Match {A}.



(* ********************************************************************** *)
(** * Auxiliary operations *)

(* BACKPORT: it would scale up better to use modules to organize the names,
   e.g. Store.empty, Store.lookup, etc.. (The C-style naming convention
   with everything flat eventually shows its limits... *)

(* ---------------------------------------------------------------------- *)
(** ** Typechecking *)

Definition store_v_same_type (A : Type) (v1 v2 : store_v A) : bool :=
  match v1, v2 with
  | Refv _, Refv _ => true
  | W8array _, W8array _ => true
  | Varray _, Varray _ => true
  | _, _ => false
  end.

Definition lit_same_type (l1 l2 : lit) : bool :=
  match l1, l2 with
    | IntLit _, IntLit _ => true
    | CharLit _, CharLit _ => true
    | StrLit _, StrLit _ => true
    | Word8Lit _, Word8Lit _ => true
    | Word64Lit _, Word64Lit _ => true
    | _, _ => false
  end.

Print TypeStamp.

Inductive stamp_same_type : stamp -> stamp -> Prop :=
| TypeStampSame : forall n nm1 nm2, stamp_same_type (TypeStamp nm1 n) (TypeStamp nm2 n)
| ExnStampSame : forall n m, stamp_same_type (ExnStamp n) (ExnStamp m).

Theorem stamp_same_type_dec : forall s1 s2, {stamp_same_type s1 s2} + {not (stamp_same_type s1 s2)}.
Proof.
  induction s1; destruct s2.
  - destruct (Nat.eq_dec n n0); subst.
    + left. constructor.
    + right. intros contra. inv contra. congruence.
  - right. intros contra. inv contra.
  - right. intros contra. inv contra.
  - left. constructor.
Defined.

(* Definition stamp_same_type (s1 s2 : stamp) : bool := *)
(*   match s1, s2 with *)
(*   | TypeStamp _ n1, TypeStamp _ n2 => if Peano_dec.eq_nat_dec n1 n2 then true else false *)
(*   | ExnStamp _, ExnStamp _ => true *)
(*   | _, _ => false *)
(*   end. *)

Inductive ctor_same_type : option stamp -> option stamp -> Prop :=
| CtorNoneSame : ctor_same_type None None
| CtorSomeSame : forall s1 s2, stamp_same_type s1 s2 ->
                          ctor_same_type (Some s1) (Some s2).

Theorem ctor_same_type_dec : forall o1 o2, {ctor_same_type o1 o2} + {not (ctor_same_type o1 o2)}.
Proof.
  intros. destruct o1; destruct o2; try (destruct s; destruct s0).
  - destruct (Nat.eq_dec n n0).
    + subst. left. constructor. constructor.
    + subst. right. intro contra. inv contra.
      inv H1. congruence.
  - right. intro contra. inv contra. inv H1.
  - right. intro contra. inv contra. inv H1.
  - left. constructor. constructor.
  - right. intro contra. inv contra.
  - right. intro contra. inv contra.
  - left. constructor.
Defined.

(* Definition ctor_same_type (c1 c2 : option stamp) : bool := *)
(*   match c1, c2 with *)
(*     | None, None => true *)
(*     | Some stamp1, Some stamp2 => stamp_same_type stamp1 stamp2 *)
(*     | _, _ => false *)
(* end. *)

(** [con_check cenv o l] asserts that the constructor (or None for a tuple) admits arity [l].
    (Note that tuples admit any arity.)
    This is an inductive version of [do_con_check] *)

Inductive con_check (cenv : env_ctor) : constr_id -> nat -> Prop :=
  | con_check_none : forall l,
      con_check cenv None l
  | con_check_some : forall n l s,
      nsLookup (ident_eq_dec _ _ string_dec string_dec) n cenv = Some (l,s) ->
      con_check cenv (Some n) l.

(* ---------------------------------------------------------------------- *)
(** ** Operations on the store *)

Definition empty_store (A : Type) : store A := [].

Definition store_lookup {A : Type} (n : nat) (st : store A) :=
  List.nth_error st n.

Definition store_alloc {A : Type} (v : store_v A) (st : store A) : (store A * nat) :=
  (st ++ [v], List.length st).

Definition store_assign_nocheck {A : Type} (n : nat) (v : store_v A) (st : store A) : store A :=
  Utils.update n v st.


(* ---------------------------------------------------------------------- *)
(** ** Operations on constructors *)

(** [con_build cenv n s] relates a constructor name [n] with its stamp [s]
    This is an inductive version of [build_conv]. *)

Inductive con_build (cenv : env_ctor) : constr_id -> option stamp -> Prop :=
  | con_build_none :
      con_build cenv None None
  | con_build_some : forall n l s,
      nsLookup (ident_eq_dec _ _ string_dec string_dec) n cenv = Some (l,s) ->
      con_build cenv (Some n) (Some s).

(* ---------------------------------------------------------------------- *)
(** ** Operations for functions *)
(* test thing: cl_env -> (optimize_sem_env cl_env (free_vars e)) *)
Definition build_rec_env (funs : list (varN * varN * exp)) (cl_env : sem_env val)
           (add_to_env : env_val) : env_val :=
  fold_right (fun '(f,x,e) env' => nsBind f (Recclosure (optimize_sem_env cl_env (free_vars e)) funs f) env') add_to_env funs.

Fixpoint find_recfun {A B : Type} (n : varN) (funs : list (varN * A * B)) : option (A * B) :=
  match funs with
  | [] => None
  | (f,x,e)::funs' => if string_dec f n then Some (x,e) else find_recfun n funs'
  end.


(* ---------------------------------------------------------------------- *)
(** ** Lookup for binary operations *)

Definition opn_lookup (op : opn) : Z -> Z -> Z :=
  match op with
  | Plus => Z.add
  | Minus => Z.sub
  | Times => Z.mul
  | Divide => Z.div
  | Modulo => Z.modulo
  end.

Definition opb_lookup (op : opb) : Z -> Z -> bool :=
  match op with
  | Lt => Z.ltb
  | Gt => Z.gtb
  | Leq => Z.leb
  | Geq => Z.geb
  end.

Definition opb_lookup_Prop (op : opb) : Z -> Z -> Prop :=
  match op with
  | Lt => Z.lt
  | Gt => Z.gt
  | Leq => Z.le
  | Geq => Z.ge
  end.

Parameter opw8_lookup : forall (op : opw), word8 -> word8 -> word8.
(* TODO: implement
  match op with
  | Andw => word_and
  | Orw  => word_or
  | Xorw => word_xor
  | Addw => word_add
  end 8.*)

Parameter opw64_lookup : forall (op : opw), word64 -> word64 -> word64.
(* TODO: implement
  match op with
  | Andw => word_and
  | Orw  => word_or
  | Xorw  => word_xor
  | Addw  => word_add
  end 64. *)

Parameter shift8_lookup : forall (op : CakeAST.shift), word8 -> nat -> word8.
(* TODO: implement
 fun w n => match op with
         | Lsl => id w
         | Lsr => id w
         | Asr => id w
         | Ror => id w
         end. *)

Parameter shift64_lookup : forall (op : CakeAST.shift), word64 -> nat -> word64.
(* TODO: implement
  fun w n => match op with
          | Lsl => id w
          | Lsr => id w
          | Asr => id w
          | Ror => id w
          end. *)


(* ---------------------------------------------------------------------- *)
(** ** Type definitions *)

Open Scope bool_scope.
Open Scope nat_scope.
Definition UniqueCtorsInDef (td : list tvarN * typeN * list (conN * list ast_t)) : Prop :=
  let '(tvs,tn,condefs) := td in
  NoDup (List.map (fun '(n,_) => n) condefs).

Definition UniqueCtorsInDefs (tds : typeDef) : Prop :=
  List.Forall UniqueCtorsInDef tds.

Definition build_constrs (s : nat) (condefs : list (conN * (list ast_t)) ) :=
  List.map (fun '(conN,ts) => (conN,(List.length ts, TypeStamp conN s))) condefs.

Fixpoint build_tdefs (next_stamp : nat) (tds : list (list tvarN * typeN * list (conN * list ast_t))) : env_ctor :=
  match tds with
  | [] => alist_to_ns []
  | (tvars,tn,condefs)::tds' => nsAppend
                                (build_tdefs (next_stamp + 1) tds')
                                (alist_to_ns (List.rev (build_constrs next_stamp condefs)))
  end.


(* ********************************************************************** *)
(** * Other auxiliary operations,
      currently not needed by RelationBigStep, but might be in the future *)

Fixpoint val_to_list (v : val) : option (list val) :=
  match v with
  | Conv (Some stamp) [] => if stamp_eq_dec stamp (TypeStamp "[]" list_type_num)
                           then Some []
                           else None
  | Conv (Some stamp) [v1;v2] => if stamp_eq_dec stamp (TypeStamp "::" list_type_num)
                                then match val_to_list v2 with
                                     | Some vs => Some (v1::vs)
                                     | None => None
                                     end
                                else None
  | _ => None
  end.

Fixpoint list_to_val (vs : list val) : val :=
  match vs with
  | [] => Conv (Some (TypeStamp "[]" list_type_num)) []
  | v'::vs' => Conv (Some (TypeStamp "::" list_type_num)) [v'; list_to_val vs']
  end.

Fixpoint val_to_char_list (v : val) : option (list char) :=
  match v with
  | Conv (Some stamp) [] => if stamp_eq_dec stamp (TypeStamp "[]" list_type_num)
                           then Some []
                           else None
  (* | Conv (Some stamp) [Litv (CharLit c); v'] => *)
  (*   if stamp_eq_dec stamp (TypeStamp "::" list_type_num) *)
  (*   then match val_to_char_list v' with *)
  (*        | Some cs => Some (c::cs) *)
  (*        | None => None *)
  (*        end *)
  (*   else None *)
  | _ => None
  end.

Fixpoint vals_to_string (vs : list val) : option String.string :=
  match vs with
  | [] => Some ""
  (* | (Litv (StrLit s1))::vs' => match vals_to_string vs' with *)
  (*                            | Some s2 => Some (String.append s1 s2) *)
  (*                            | None => None *)
  (*                            end *)
  | _ => None
  end.

Open Scope bool_scope.
Open Scope Z_scope.

Fixpoint copy_array {A : Type} (p : list A * Z) (len : Z)
         (op : option (list A * Z)) : option (list A) :=
  let '(src,srcoff) := p in
  if sumbool_or _ _ _ _ (Z_lt_dec srcoff 0) (sumbool_or _ _ _ _ (Z_lt_dec len 0) (Z_lt_dec (Zlength src) (srcoff + len)))
    then None
     else let copied := List.firstn (Z.to_nat len)
                         (List.skipn (Z.to_nat srcoff) src) in
           match op with
           | Some (dst,dstoff) =>
             if sumbool_or _ _ _ _ (Z_lt_dec dstoff 0)  (Z_lt_dec (Zlength dst) (dstoff + len))
               then None
               else Some (List.firstn
                            (Z.to_nat dstoff)
                            dst ++ copied ++
                            List.skipn (Z.to_nat (dstoff + len)) dst)
           | None => Some copied
   end.

Close Scope bool_scope.
Close Scope Z_scope.


(* ********************************************************************** *)
(** * Induction principles *)

(* ---------------------------------------------------------------------- *)
(** ** Induction for values *)

Fixpoint val_rect (P : val -> Type)
         (* (H1 : forall (l : lit), P (Litv l)) *)
         (H2 : forall (o : option stamp) (l : list val), Forall''  P l -> P (Conv o l))
         (H3 : forall (s : sem_env val) (n : varN) (e : exp), Forall'' (fun p => P (snd p)) (sev s) -> P (Closure s n e))
         (H4 : forall (s : sem_env val) (l : list (varN * varN * exp)) (n : varN), Forall'' (fun p => P (snd p)) (sev s) ->
                                                                            P (Recclosure s l n))
         (* (H5 : forall (n : nat), P (Loc n)) *)
         (* (H6 : forall (l : list val), Forall'' P l -> P (Vectorv l)) *)
         (v : val) : P v :=
  let val_rect' := @val_rect P H2 H3 H4 in
  match v with
  (* | Litv l => H1 l *)
  | Conv o l => let fix loop (l : list val) :=
                   match l with
                   | [] => Forall_nil'' val P
                   | h::t => Forall_cons'' val P h t (val_rect' h) (loop t)
                   end
               in
               H2 o l (loop l)
  | Closure s n e => let fix loop__ns (ls : namespace modN varN val) :=
                        match ls with
                          | [] => Forall_nil'' (ident modN varN * val) (fun p => P (snd p))
                          | ((i,v'))::ls' => Forall_cons'' (ident modN varN * val) (fun p => P (snd p))
                                                       (i,v') ls' (val_rect' v') (loop__ns ls')
                        end
                    in
                    H3 s n e (loop__ns (sev s))
  | Recclosure s l n => let fix loop__ns (ls : namespace modN varN val) :=
                           match ls with
                           | [] => Forall_nil'' (ident modN varN * val) (fun p => P (snd p))
                           | ((i,v'))::ls' => Forall_cons'' (ident modN varN * val) (fun p => P (snd p))
                                                         (i,v') ls' (val_rect' v') (loop__ns ls')
                           end
                       in
                       H4 s l n (loop__ns (sev s))
  (* | Loc n => H5 n *)
  (* | Vectorv l => let fix loop (l : list val) := *)
  (*                   match l with *)
  (*                   | [] => Forall_nil'' val P *)
  (*                   | h::t => Forall_cons'' val P h t (val_rect' h) (loop t) *)
  (*                   end *)
  (*               in *)
  (*               H6 l (loop l) *)
  end.

Definition val_ind (P : val -> Prop) := @val_rect P.
Definition val_rec (P : val -> Set) := @val_rect P.

(** Decidability theorems *)

Theorem val_eq_dec : forall (v0 v1 : val), {v0 = v1} + {v0 <> v1}.
Proof.
  decide equality; auto with DecidableEquality.
  - generalize dependent l0. induction l; destruct l0; try (left; reflexivity); try (right; discriminate).
    inversion X; subst; clear X. destruct (X0 v); destruct (IHl X1 l0); subst; try (right; discriminate); try (left; reflexivity).
    right; injection; assumption.
    right; injection; assumption.
    right; injection. intro. assumption.
  - generalize dependent s0. induction s; destruct s0.

    assert (pair_nat_stamp_dec : forall (p p0: (nat * stamp)), {p = p0} + {p <> p0})
      by (decide equality; auto with DecidableEquality).
    destruct (namespace_eq_dec modN conN (nat * stamp) String.string_dec String.string_dec
                               pair_nat_stamp_dec sec0 sec1); subst.

    generalize dependent sev1.
    simpl in X.
    induction X; destruct sev1; try (left; reflexivity); try (right; discriminate).
    destruct x; destruct p0.
    destruct (ident_eq_dec modN varN string_dec string_dec i i0); subst.
    destruct (p v3); subst.
    simpl in *.
    destruct (IHX sev1).
    inversion e1.
    left; reflexivity.
    right; intro con; inversion con. apply n0. rewrite H0. reflexivity.
    right; intro con; inversion con; auto.
    right; intro con; inversion con; auto.
    right; intro con; inversion con; auto.
  - generalize dependent s0. induction s; destruct s0.

    assert (pair_nat_stamp_dec : forall (p p0: (nat * stamp)), {p = p0} + {p <> p0})
      by (decide equality; auto with DecidableEquality).
    destruct (namespace_eq_dec modN conN (nat * stamp) String.string_dec String.string_dec
                               pair_nat_stamp_dec sec0 sec1); subst.

    simpl in X.
    generalize dependent sev1.
    induction X; destruct sev1; try (left; reflexivity); try (right; discriminate).
    destruct x; destruct p0.
    destruct (ident_eq_dec modN varN string_dec string_dec i i0); subst.
    destruct (p v3); subst.
    simpl in *.
    destruct (IHX sev1).
    inversion e.
    left; reflexivity.
    right; intro con; inversion con. apply n0. rewrite H0. reflexivity.
    right; intro con; inversion con; auto.
    right; intro con; inversion con; auto.
    right; intro con; inversion con; auto.
Defined.
(*   - generalize dependent l0. induction l; destruct l0; try (left; reflexivity); try (right; discriminate). *)
(*     inversion X; subst; clear X. destruct (X0 v); destruct (IHl X1 l0); subst; try (right; discriminate); try (left; reflexivity). *)
(*     right; injection; assumption. *)
(*     right; injection; assumption. *)
(*     right; injection. intro. assumption. *)
(* Defined. *)

Lemma UniqueCtorsInDef_dec : forall (td : (list tvarN * typeN * list (conN * list ast_t))),
    {UniqueCtorsInDef td} + {~ UniqueCtorsInDef td}.
Proof.
  unfold UniqueCtorsInDef. intro td.
  destruct td. destruct p.
  apply NoDuplicates_dec.
  auto with DecidableEquality.
Defined.

Theorem UniqueCtorsInDefs_dec : forall (tds : typeDef), {UniqueCtorsInDefs tds} + {~ UniqueCtorsInDefs tds}.
Proof.
  apply Forall_dec.
  apply UniqueCtorsInDef_dec.
Defined.
