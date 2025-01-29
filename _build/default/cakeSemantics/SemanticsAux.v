Require Import Bool.Sumbool.
Require Import List.
Import ListNotations.
Require Import ZArith.

Require Import CakeSem.Utils.
Require Import CakeSem.CakeAST.
Require Import CakeSem.Namespace.
Require Import CakeSem.ffi.FFI.

Open Scope string_scope.
Open Scope list_scope.

Set Implicit Arguments.
(* ********************************************************************** *)
(** * Auxiliary semantics constructs *)

(* ---------------------------------------------------------------------- *)
(** ** Stamps and predefined constructors *)

(* constructor name and unique type number *)
Inductive stamp : Type :=
  | TypeStamp : conN -> nat -> stamp
  | ExnStamp : nat -> stamp.
Scheme Equality for stamp.
#[export] Hint Resolve stamp_eq_dec : DecidableEquality.

(* ---------------------------------------------------------------------- *)
(** ** Environments *)
(* QUESTION: what is the interest of being generic in the type of values? *)
(* ANSWER: I DON'T EVEN KNOW, but also we havent defined our values yet *)

Record sem_env (V : Type) := {
  sev : namespace modN varN V;
  (* nat is the arity of the constructor name conN *)
  sec : namespace modN conN (nat * stamp) }.

Arguments sev {V} _.
Arguments sec {V} _.

(* TODO: Move to theorems file? *)
Theorem sem_env_id : forall (V : Type) (env : sem_env V), env = {| sev := sev env; sec := sec env|}.
Proof. destruct env; reflexivity.  Qed.

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

(* ---------------------------------------------------------------------- *)
(** ** Values *)

Unset Elimination Schemes.

(* TODO: HOL4 version now supports floating point and a repl *)
Inductive val : Type :=
  | Litv : lit -> val
  | Conv : option stamp -> list val -> val
  | Closure : sem_env val -> varN -> exp -> val
  | Recclosure : sem_env val -> list (varN * varN * exp) -> varN -> val
  | Loc : nat -> val
  | Vectorv : list val -> val.

Set Elimination Schemes.
Definition env_val := namespace modN varN val.
Definition env_ctor := namespace modN conN (nat * stamp).

(** [is_closure v] captures whether [v] is a closure or a recursive closure. *)
Definition is_closureb (v : val) : bool :=
  match v with
  | Closure _ _ _ => true
  | Recclosure _ _ _ => true
  | _ => false
  end.

Definition is_closure (v : val) : Prop :=
  match v with
  | Closure _ _ _ => True
  | Recclosure _ _ _ => True
  | _ => False
  end.

(* ---------------------------------------------------------------------- *)
(** ** Predefined exceptions and constructors  *)
(* BACKPORT: bind_stamp is used to mean "match failure", but that's not an intuitive name for it *)
Definition bind_stamp := ExnStamp 0.
Definition chr_stamp := ExnStamp 1.
Definition div_stamp := ExnStamp 2.
Definition subscript_stamp := ExnStamp 3.


Definition bind_exn_v := Conv (Some bind_stamp) [].
Definition chr_exn_v  := Conv (Some chr_stamp) [].
Definition div_exn_v  := Conv (Some div_stamp) [].
Definition sub_exn_v  := Conv (Some subscript_stamp) [].

Definition bool_type_num := 0.
Definition list_type_num := 1.
Definition option_type_num := 2.

(* BACKPORT: define these 3 shorthands *)

Definition ConvTrue := Conv (Some (TypeStamp "True"  bool_type_num)) [].
Definition ConvFalse := Conv (Some (TypeStamp "False"  bool_type_num)) [].
Definition ConvUnit := Conv None [].

Definition Boolv (b : bool) : val :=
  if b then ConvTrue  else ConvFalse.

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

Definition stamp_same_type (s1 s2 : stamp) : bool :=
  match s1, s2 with
  | TypeStamp _ n1, TypeStamp _ n2 => Nat.eqb n1 n2
  | ExnStamp _, ExnStamp _ => true
  | _, _ => false
  end.

Definition ctor_same_type (os1 os2 : option stamp) : bool :=
  match os1, os2 with
  | None, None => true
  | Some s1, Some s2 => stamp_same_type s1 s2
  | _, _ => false
end.

(** [con_check cenv o l] asserts that the constructor (or None for a tuple) admits arity [l].
    (Note that tuples admit any arity.)
    This is an inductive version of [do_con_check] *)
Definition do_con_check (cenv : env_ctor) (cid : constr_id) (l : nat) : bool :=
  match cid with
  | None => true
  | Some id => match nsLookup (ident_beq _ _ String.eqb String.eqb) id cenv with
              | None => false
              | Some (l',s) => Nat.eqb l' l
              end
  end.

(* ---------------------------------------------------------------------- *)
(** ** Operations on the store *)

Definition empty_store (A : Type) : store A := [].
Arguments empty_store {A}.

Definition store_lookup {A : Type} (n : nat) (st : store A) :=
  List.nth_error st n.

Definition store_alloc {A : Type} (v : store_v A) (st : store A) : (store A * nat) :=
  (st ++ [v], List.length st).

Definition store_assign_nocheck {A : Type} (n : nat) (v : store_v A) (st : store A) : store A :=
  Utils.update n v st.

(* ---------------------------------------------------------------------- *)
(** ** Operations on constructors *)

Definition build_conv (cenv : env_ctor) (cid : constr_id) (vs: list val) : option val :=
  match cid with
  | None => Some (Conv None vs)
  | Some id => match nsLookup (ident_beq _ _ String.eqb String.eqb) id cenv with
              | None => None
              | Some (len,stmp) => Some (Conv (Some stmp) vs)
              end
  end.

(* ---------------------------------------------------------------------- *)
(** ** Operations for functions *)
Definition build_rec_env (funs : list (varN * varN * exp)) (cl_env : sem_env val)
           (add_to_env : env_val) : env_val :=
  fold_right (fun '(f,x,e) env' => nsBind f (Recclosure cl_env funs f) env') add_to_env funs.

Fixpoint find_recfun {A B : Type} (n : varN) (funs : list (varN * A * B)) : option (A * B) :=
  match funs with
  | [] => None
  | (f,x,e)::funs' => if String.eqb f n then Some (x,e) else find_recfun n funs'
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
(* Definition UniqueCtorsInDef (td : list tvarN * typeN * list (conN * list ast_t)) : Prop := *)
(*   let '(tvs,tn,condefs) := td in *)
(*   NoDup (List.map (fun '(n,_) => n) condefs). *)

(* Definition UniqueCtorsInDefs (tds : typeDef) : Prop := *)
(*   List.Forall UniqueCtorsInDef tds. *)

Fixpoint string_in (s : string) (l : list string) : bool :=
  match l with
  | [] => false
  | s'::l' => if String.eqb s s' then
              true
            else string_in s l'
  end.

Fixpoint nodup_str (ls : list string) : bool :=
  match ls with
  | [] => true
  | s::ls' => if string_in s ls' then
              false
            else nodup_str ls'
  end.

Definition unique_ctors_in_def (td : list tvarN * typeN * list (conN * list ast_t)) : bool :=
  let '(tvs,tn,condefs) := td in
  nodup_str (List.map (fun '(n,_) => n) condefs).

Definition unique_ctros_in_defs (tds : typeDef) : bool :=
  forallb unique_ctors_in_def tds.

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
  | Conv (Some stamp) [] => if stamp_beq stamp (TypeStamp "[]" list_type_num)
                           then Some []
                           else None
  | Conv (Some stamp) [v1;v2] => if stamp_beq stamp (TypeStamp "::" list_type_num)
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
  | Conv (Some stamp) [] => if stamp_beq stamp (TypeStamp "[]" list_type_num)
                           then Some []
                           else None
  | Conv (Some stamp) [Litv (CharLit c); v'] =>
    if stamp_beq stamp (TypeStamp "::" list_type_num)
    then match val_to_char_list v' with
         | Some cs => Some (c::cs)
         | None => None
         end
    else None
  | _ => None
  end.

Fixpoint vals_to_string (vs : list val) : option String.string :=
  match vs with
  | [] => Some ""
  | (Litv (StrLit s1))::vs' => match vals_to_string vs' with
                             | Some s2 => Some (String.append s1 s2)
                             | None => None
                             end
  | _ => None
  end.

Open Scope bool_scope.
Open Scope Z_scope.

Definition copy_array {A : Type} (p : list A * Z) (len : Z)
                      (op : option (list A * Z)) : option (list A) :=
  let (src,srcoff) := p in
  if (srcoff =? 0) || (len <? 0) || (Zlength src <? srcoff + len)
  then None
  else let copied := List.firstn (Z.to_nat len)
                       (List.skipn (Z.to_nat srcoff) src) in
       match op with
       | Some (dst,dstoff) => if (dstoff <? 0) || (Zlength dst <? dstoff + len)
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
         (H1 : forall (l : lit), P (Litv l))
         (H2 : forall (o : option stamp) (l : list val), Forall''  P l -> P (Conv o l))
         (H3 : forall (s : sem_env val) (n : varN) (e : exp), Forall'' (fun p => P (snd p)) (sev s) -> P (Closure s n e))
         (H4 : forall (s : sem_env val) (l : list (varN * varN * exp)) (n : varN), Forall'' (fun p => P (snd p)) (sev s) ->
                                                                            P (Recclosure s l n))
         (H5 : forall (n : nat), P (Loc n))
         (H6 : forall (l : list val), Forall'' P l -> P (Vectorv l))
         (v : val) : P v :=
  let val_rect' := @val_rect P H1 H2 H3 H4 H5 H6 in
  match v with
  | Litv l => H1 l
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
  | Loc n => H5 n
  | Vectorv l => let fix loop (l : list val) :=
                    match l with
                    | [] => Forall_nil'' val P
                    | h::t => Forall_cons'' val P h t (val_rect' h) (loop t)
                    end
                in
                H6 l (loop l)
  end.

Definition val_ind (P : val -> Prop) := @val_rect P.
Definition val_rec (P : val -> Set) := @val_rect P.

Fixpoint val_beq (v1 v2 : val) : bool :=
  match v1, v2 with
  | Litv l1, Litv l2 => lit_beq l1 l2
  | Conv o1 l1, Conv o2 l2 => andb (option_beq _ stamp_beq o1 o2) (list_beq val_beq l1 l2)
  (* not real equality, but considered equivalent by CakeML*)
  | Closure env1 v1 e1, Closure env2 v2 e2 => true
  | Recclosure env1 l1 v1, Recclosure env2 l2 v2 => true
  | Loc n1, Loc n2 => n1 =? n2
  | Vectorv l1, Vectorv l2 => list_beq val_beq l1 l2
  | _, _ => false
  end.

(** Decidability theorems *)

(* Theorem val_eq_dec : forall (v0 v1 : val), {v0 = v1} + {v0 <> v1}. *)
(* Proof. *)
(*   decide equality; auto with DecidableEquality. *)
(*   - generalize dependent l0. induction l; destruct l0; try (left; reflexivity); try (right; discriminate). *)
(*     inversion X; subst; clear X. destruct (X0 v); destruct (IHl X1 l0); subst; try (right; discriminate); try (left; reflexivity). *)
(*     right; injection; assumption. *)
(*     right; injection; assumption. *)
(*     right; injection. intro. assumption. *)
(*   - generalize dependent s0. induction s; destruct s0. *)

(*     assert (pair_nat_stamp_dec : forall (p p0: (nat * stamp)), {p = p0} + {p <> p0}) *)
(*       by (decide equality; auto with DecidableEquality). *)
(*     destruct (namespace_eq_dec modN conN (nat * stamp) String.string_dec String.string_dec *)
(*                                pair_nat_stamp_dec sec0 sec1); subst. *)

(*     generalize dependent sev1. *)
(*     simpl in X. *)
(*     induction X; destruct sev1; try (left; reflexivity); try (right; discriminate). *)
(*     destruct x; destruct p0. *)
(*     destruct (ident_eq_dec modN varN string_dec string_dec i i0); subst. *)
(*     destruct (p v3); subst. *)
(*     simpl in *. *)
(*     destruct (IHX sev1). *)
(*     inversion e1. *)
(*     left; reflexivity. *)
(*     right; intro con; inversion con. apply n0. rewrite H0. reflexivity. *)
(*     right; intro con; inversion con; auto. *)
(*     right; intro con; inversion con; auto. *)
(*     right; intro con; inversion con; auto. *)
(*   - generalize dependent s0. induction s; destruct s0. *)

(*     assert (pair_nat_stamp_dec : forall (p p0: (nat * stamp)), {p = p0} + {p <> p0}) *)
(*       by (decide equality; auto with DecidableEquality). *)
(*     destruct (namespace_eq_dec modN conN (nat * stamp) String.string_dec String.string_dec *)
(*                                pair_nat_stamp_dec sec0 sec1); subst. *)

(*     simpl in X. *)
(*     generalize dependent sev1. *)
(*     induction X; destruct sev1; try (left; reflexivity); try (right; discriminate). *)
(*     destruct x; destruct p0. *)
(*     destruct (ident_eq_dec modN varN string_dec string_dec i i0); subst. *)
(*     destruct (p v3); subst. *)
(*     simpl in *. *)
(*     destruct (IHX sev1). *)
(*     inversion e. *)
(*     left; reflexivity. *)
(*     right; intro con; inversion con. apply n0. rewrite H0. reflexivity. *)
(*     right; intro con; inversion con; auto. *)
(*     right; intro con; inversion con; auto. *)
(*     right; intro con; inversion con; auto. *)
(*   - generalize dependent l0. induction l; destruct l0; try (left; reflexivity); try (right; discriminate). *)
(*     inversion X; subst; clear X. destruct (X0 v); destruct (IHl X1 l0); subst; try (right; discriminate); try (left; reflexivity). *)
(*     right; injection; assumption. *)
(*     right; injection; assumption. *)
(*     right; injection. intro. assumption. *)
(* Defined. *)


(* Lemma UniqueCtorsInDef_dec : forall (td : (list tvarN * typeN * list (conN * list ast_t))), *)
(*     {UniqueCtorsInDef td} + {~ UniqueCtorsInDef td}. *)
(* Proof. *)
(*   unfold UniqueCtorsInDef. intro td. *)
(*   destruct td. destruct p. *)
(*   apply NoDuplicates_dec. *)
(*   auto with DecidableEquality. *)
(* Defined. *)

(* Theorem UniqueCtorsInDefs_dec : forall (tds : typeDef), {UniqueCtorsInDefs tds} + {~ UniqueCtorsInDefs tds}. *)
(* Proof. *)
(*   apply Forall_dec. *)
(*   apply UniqueCtorsInDef_dec. *)
(* Defined. *)
