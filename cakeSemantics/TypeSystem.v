Require Import Utils.
Require Import Namespace.
Require Import CakeAST.
Require Import SemanticsAux.
Require Import Lists.List.
Import ListNotations.
Require Import PeanoNat.
Require Import Strings.String.
Require Import Bool.
Require Import Evaluate.

Definition type_ident := nat.

Unset Elimination Schemes.
Inductive t : Set :=
  (* Type variables that the user writes down ('a, 'b, etc.) *)
  | Tvar : tvarN -> t
  (* deBruijn indexed type variables. *)
  | Tvar_db : nat -> t
  (* The two numbers represent the identity of the type constructor. The first
     is the identity of the compilation unit that it was defined in, and the
     second is its identity inside of that unit *)
  | Tapp : list t -> type_ident -> t.
Set Elimination Schemes.

Fixpoint t_rect (P : t -> Type)
         (H1 : forall (tv : tvarN), P (Tvar tv))
         (H2 : forall (n : nat), P (Tvar_db n))
         (H3 : forall (ts : list t) (n : nat), Forall'' P ts -> P (Tapp ts n))
         (ty : t) : P ty :=
  match ty return (P ty) with
  | Tvar tv => H1 tv
  | Tvar_db n => H2 n
  | Tapp ts n => let fix loop (l : list t) :=
                    match l with
                    | [] => Forall_nil'' t P
                    | h::tl => Forall_cons'' t P h tl (t_rect P H1 H2 H3 h) (loop tl)
                    end
                in
                H3 ts n (loop ts)
  end.

Definition t_rec (P : t -> Set) := t_rect P.
Definition t_ind (P : t -> Prop) := t_rect P.

Theorem t_eq_dec : forall (t1 t2 : t), {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality; auto with DecidableEquality.
  revert l. induction X.
  - destruct l; try (right; congruence); try (left; congruence).
  - destruct l0; try (right; congruence).
    destruct (p t3); try (right; congruence).
    destruct (IHX l0); try (right; congruence).
    subst. left; reflexivity.
Defined.

(* Some abbreviations *)
Definition Tarray_num : type_ident := 0.
Definition Tbool_num : type_ident := 1.
Definition Tchar_num : type_ident := 2.
Definition Texn_num : type_ident := 3.
Definition Tfn_num : type_ident := 4.
Definition Tint_num : type_ident := 5.
Definition Tlist_num : type_ident := 6.
Definition Tref_num : type_ident := 7.
Definition Tstring_num : type_ident := 8.
Definition Ttup_num : type_ident := 9.
Definition Tvector_num : type_ident := 10.
Definition Tword64_num : type_ident := 11.
Definition Tword8_num : type_ident := 12.
Definition Tword8array_num : type_ident := 13.

(* The numbers for the primitive types *)
Definition prim_type_nums :=
  [Tarray_num; Tchar_num; Texn_num; Tfn_num; Tint_num; Tref_num; Tstring_num; Ttup_num;
   Tvector_num; Tword64_num; Tword8_num; Tword8array_num].

Definition Tarray t := Tapp [t] Tarray_num.
Definition Tbool := Tapp [] Tbool_num.
Definition Tchar := Tapp [] Tchar_num.
Definition Texn := Tapp [] Texn_num.
Definition Tfn t1 t2 := Tapp [t1;t2] Tfn_num.
Definition Tint := Tapp [] Tint_num.
Definition Tlist t := Tapp [t] Tlist_num.
Definition Tref t := Tapp [t] Tref_num.
Definition Tstring := Tapp [] Tstring_num.
Definition Ttup ts := Tapp ts Ttup_num.
Definition Tvector t := Tapp [t] Tvector_num.
Definition Tword64 := Tapp [] Tword64_num.
Definition Tword8 := Tapp [] Tword8_num.
Definition Tword8array := Tapp [] Tword8array_num.

(* Check that the free type variables are in the given list. Every deBruijn
 * variable must be smaller than the first argument. So if it is 0, no deBruijn
 * indices are permitted. *)
Fixpoint elem (A : Type) (adec : forall (a b : A), {a=b} + {a <> b}) (e : A) (l : list A) : bool :=
  match l with
  | [] => false
  | e'::l' => if adec e e' then true else elem A adec e l'
  end.

Fixpoint check_freevars (dbmax : nat) (tvs: list tvarN) (ty : t) : bool :=
  match ty with
  | Tvar tv => elem string string_dec tv tvs
  | Tapp ts tn => forallb (check_freevars dbmax tvs) ts
  | Tvar_db n => n <? dbmax
  end.

Fixpoint check_freevars_ast (tvs : list tvarN) (ast : ast_t) : bool :=
  match ast with
  (* | Atvar ty => true (* elem tv tvs *) *)
  (* | Attup ts => true (* List.all (check_freevars_ast tvs) ts *) *)
  (* | Atfun t1 t2 => true (* check_freevars_ast tvs t1 && check_freevars_ast tvs t2 *) *)
  | Atapp ts tn => forallb (check_freevars_ast tvs) ts
  end.


Check alist.
Check lookup.
Print lookup.
(* Simultaneous substitution of types for type variables in a type *)
Fixpoint type_subst (l : alist tvarN t) (ty : t) : t :=
  match ty with
  | Tvar tv => match lookup string_dec tv l with
              | None => Tvar tv
              | Some t => t
              end
  | Tapp ts tn => Tapp (map (type_subst l) ts) tn
  | Tvar_db n => Tvar_db n
  end.

(* Increment the deBruijn indices in a type by n levels, skipping all levels
 * less than skip. *)
Fixpoint deBruijn_inc (skip n : nat) (ty : t) : t :=
  match ty with
  | Tvar tv => Tvar tv
  | Tvar_db m => if m <? skip then Tvar_db m else Tvar_db (m+n)
  | Tapp ts tn => Tapp (map (deBruijn_inc skip n) ts) tn
  end.

(* skip the lowest given indices and replace the next (LENGTH ts) with the given types and reduce all the higher ones *)
(* Pre: length ts <= n *)
Fixpoint deBruijn_subst (skip : nat) (ts : list t) (ty : t) : t :=
  match ty with
  | Tvar tv => Tvar tv
  | Tvar_db n => if negb (n <? skip) && (n <? List.length ts + skip)
                then nth (n - skip) ts (Tvar_db n)
                else if negb (n <? skip)
                     then Tvar_db (n - List.length ts)
                     else Tvar_db n
  | Tapp ts' tn => Tapp (map (deBruijn_subst skip ts) ts') tn
  end.

(* Type environments *)
Inductive tenv_val_exp : Set :=
  | Empty : tenv_val_exp
  (* Binds several de Bruijn type variables *)
  | Bind_tvar : nat -> tenv_val_exp -> tenv_val_exp
  (* The number is how many de Bruijn type variables the typescheme binds *)
  | Bind_name : varN -> nat -> t -> tenv_val_exp -> tenv_val_exp.

Definition bind_tvar (tvs : nat) (tenvE : tenv_val_exp) : tenv_val_exp :=
  if tvs =? 0 then tenvE else Bind_tvar tvs tenvE.

Definition opt_bind_name (n : option varN) (tvs : nat) (ty : t) (tenvE : tenv_val_exp)
  : tenv_val_exp :=
  match n with
  | None => tenvE
  | Some n' => Bind_name n' tvs ty tenvE
  end.

Fixpoint tveLookup (n : varN) (inc : nat) (tenvE : tenv_val_exp) : option (nat * t) :=
  match tenvE with
  | Empty => None
  | Bind_tvar tvs tenvE' => tveLookup n (inc + tvs) tenvE'
  | Bind_name n' tvs ty tenvE' => if string_dec n' n
                                  then Some (tvs, deBruijn_inc tvs inc ty)
                                  else tveLookup n inc tenvE'
  end.

Definition tenv_abbrev := namespace modN typeN (list tvarN * t).
Definition tenv_ctor := namespace modN conN (list tvarN * list t * type_ident).
Definition tenv_val := namespace modN varN (nat * t).

Record type_env := mktype_env
   { tev : tenv_val
   ; tec : tenv_ctor
   ; tet : tenv_abbrev
   }.

Definition extend_dec_tenv (tenv' tenv : type_env) : type_env :=
  {| tev := nsAppend (tev tenv') (tev tenv);
     tec := nsAppend (tec tenv') (tec tenv);
     tet := nsAppend (tet tenv') (tet tenv) |}.

Definition lookup_varE (id : ident modN varN) (tenvE : tenv_val_exp) : option (nat * t) :=
  match id with
  | Short x => tveLookup x 0 tenvE
  | _ => None
  end.

Definition lookup_var (id : ident modN varN) (tenvE : tenv_val_exp) (tenv : type_env) : option (nat * t) :=
  match lookup_varE id tenvE with
  | Some x as s => s
  | None => nsLookup ident_string_dec id (tev tenv)
  end.

Fixpoint num_tvs (tenvE : tenv_val_exp) : nat :=
  match tenvE with
  | Empty => 0
  | Bind_tvar tvs tenvE' => tvs + num_tvs tenvE'
  | Bind_name n tvs t tenvE' => num_tvs tenvE'
  end.

Fixpoint bind_var_list (tvs : nat) (vtl : list (varN * t)) (tenvE : tenv_val_exp) : tenv_val_exp :=
  match vtl with
  | [] => tenvE
  | (n,t)::binds => Bind_name n tvs t (bind_var_list tvs binds tenvE)
  end.

(* Check that the operator can have type (t1 -> ... -> tn -> t) *)
Definition type_op (o : op) (ts : list t) (ty : t) : bool :=
  match o,ts with
    | Opapp, [t1; t2] => if t_eq_dec t1 (Tfn t2 ty) then true else false
    (* | (Opn _, [t1; t2]) -> t1 = Tint && t2 = Tint && t = Tint *)
    (* | (Opb _, [t1; t2]) -> t1 = Tint && t2 = Tint && t = Tbool *)
    (* | (Opw W8 _, [t1; t2]) -> t1 = Tword8 && t2 = Tword8 && t = Tword8 *)
    (* | (Opw W64 _, [t1; t2]) -> t1 = Tword64 && t2 = Tword64 && t = Tword64 *)
    (* | (FP_top _, [t1; t2; t3]) -> t1 = Tword64 && t2 = Tword64 && t3 = Tword64 && t = Tword64 *)
    (* | (FP_bop _, [t1; t2]) -> t1 = Tword64 && t2 = Tword64 && t = Tword64 *)
    (* | (FP_uop _, [t1]) ->  t1 = Tword64 && t = Tword64 *)
    (* | (FP_cmp _, [t1; t2]) ->  t1 = Tword64 && t2 = Tword64 && t = Tbool *)
    (* | (Shift W8 _ _, [t1]) -> t1 = Tword8 && t = Tword8 *)
    (* | (Shift W64 _ _, [t1]) -> t1 = Tword64 && t = Tword64 *)
    (* | (Equality, [t1; t2]) -> t1 = t2 && t = Tbool *)
    (* | (Opassign, [t1; t2]) -> t1 = Tref t2 && t = Ttup [] *)
    (* | (Opref, [t1]) -> t = Tref t1 *)
    (* | (Opderef, [t1]) -> t1 = Tref t *)
    (* | (Aw8alloc, [t1; t2]) -> t1 = Tint && t2 = Tword8 && t = Tword8array *)
    (* | (Aw8sub, [t1; t2]) -> t1 = Tword8array && t2 = Tint && t = Tword8 *)
    (* | (Aw8length, [t1]) -> t1 = Tword8array && t = Tint *)
    (* | (Aw8update, [t1; t2; t3]) -> t1 = Tword8array && t2 = Tint && t3 = Tword8 && t = Ttup [] *)
    (* | (WordFromInt W8, [t1]) -> t1 = Tint && t = Tword8 *)
    (* | (WordToInt W8, [t1]) -> t1 = Tword8 && t = Tint *)
    (* | (WordFromInt W64, [t1]) -> t1 = Tint && t = Tword64 *)
    (* | (WordToInt W64, [t1]) -> t1 = Tword64 && t = Tint *)
    (* | (CopyStrStr, [t1; t2; t3]) -> t1 = Tstring && t2 = Tint && t3 = Tint && t = Tstring *)
    (* | (CopyStrAw8, [t1; t2; t3; t4; t5]) -> *)
    (*   t1 = Tstring && t2 = Tint && t3 = Tint && t4 = Tword8array && t5 = Tint && t = Ttup [] *)
    (* | (CopyAw8Str, [t1; t2; t3]) -> t1 = Tword8array && t2 = Tint && t3 = Tint && t = Tstring *)
    (* | (CopyAw8Aw8, [t1; t2; t3; t4; t5]) -> *)
    (*   t1 = Tword8array && t2 = Tint && t3 = Tint && t4 = Tword8array && t5 = Tint && t = Ttup [] *)
    (* | (Chr, [t1]) -> t1 = Tint && t = Tchar *)
    (* | (Ord, [t1]) -> t1 = Tchar && t = Tint *)
    (* | (Chopb _, [t1; t2]) -> t1 = Tchar && t2 = Tchar && t = Tbool *)
    (* | (Implode, [t1]) -> t1 = Tlist Tchar && t = Tstring *)
    (* | (Explode, [t1]) -> t1 = Tstring && t = Tlist Tchar *)
    (* | (Strsub, [t1; t2]) -> t1 = Tstring && t2 = Tint && t = Tchar *)
    (* | (Strlen, [t1]) -> t1 = Tstring && t = Tint *)
    (* | (Strcat, [t1]) -> t1 = Tlist Tstring && t = Tstring *)
    (* | (VfromList, [Tapp [t1] ctor]) -> ctor = Tlist_num && t = Tvector t1 *)
    (* | (Vsub, [t1; t2]) -> t2 = Tint && Tvector t = t1 *)
    (* | (Vlength, [Tapp [t1] ctor]) -> ctor = Tvector_num && t = Tint *)
    (* | (Aalloc, [t1; t2]) -> t1 = Tint && t = Tarray t2 *)
    (* | (AallocEmpty, [t1]) -> t1 = Ttup [] && exists t2. t = Tarray t2 *)
    (* | (Asub, [t1; t2]) -> t2 = Tint && Tarray t = t1 *)
    (* | (Alength, [Tapp [t1] ctor]) -> ctor = Tarray_num && t = Tint *)
    (* | (Aupdate, [t1; t2; t3]) -> t1 = Tarray t3 && t2 = Tint && t = Ttup [] *)
    (* | (ConfigGC, [t1;t2]) -> t1 = Tint && t2 = Tint && t = Ttup [] *)
    (* | (FFI n, [t1;t2]) -> t1 = Tstring && t2 = Tword8array && t = Ttup [] *)
    (* | (ListAppend, [Tapp [t1] ctor; t2]) -> ctor = Tlist_num && t2 = Tapp [t1] ctor && t = t2 *)
    | _,_ => false
  end.

Definition check_type_names (tenvT : tenv_abbrev) (ast : ast_t) : bool :=
  match ast with
  | Atapp ts tn => match nsLookup ident_string_dec tn tenvT with
                      | Some (tvs,_) => List.length tvs =? List.length ts
                      | None => false
                    end
  end.
(* Substitution of type names for the type they abbreviate *)
Fixpoint type_name_subst (tenvT : tenv_abbrev) (ts : ast_t) : t :=
  match ts with
  | Atapp ts' tc => let args := map (type_name_subst tenvT) ts' in
                   match nsLookup ident_string_dec tc tenvT with
                   | Some (tvs, ty) => type_subst (combine tvs args) ty
                   | None => Ttup args
                   end
  end.

(* Check that a type definition defines no already defined types or duplicate
 * constructors, and that the free type variables of each constructor argument
 * type are included in the type's type parameters. Also check that all of the
 * types mentioned are in scope. *)
Check ([], "a", []).
Fixpoint check_ctor_tenv (tenvT : tenv_abbrev) (tds : list (list tvarN * typeN * list (conN * list ast_t))) : bool :=
  match tds with
  | [] => true
  | (tvs,tn,ctors)::tds' => if UniqueCtorsInDef_dec (tvs,tn,ctors)
                          then if NoDuplicates_dec string_dec tvs
                               then if forallb (fun cnts => let (cn,ts) := (cnts : conN * list ast_t) in (forallb (check_freevars_ast tvs) ts) && (forallb (check_type_names tenvT) ts)) ctors
                                    then if negb (elem string string_dec tn
                                                       (map (fun trip => match trip with
                                                                      | (_,tn,_) => tn
                                                                      end)
                                                                tds'))
                                         then check_ctor_tenv tenvT tds'
                                         else false
                                    else false
                               else false
                          else false
  end.


Fixpoint build_ctor_tenv (tenvT : tenv_abbrev) (tds : list (list tvarN * typeN * list (conN * list ast_t))) (ids : list nat)
  : tenv_ctor :=
  match tds, ids with
  | [], [] => []
  | (tvs,tn,ctors)::tds', id::ids' => nsAppend
                                     (build_ctor_tenv tenvT tds' ids')
                                     (alist_to_ns
                                        (rev
                                           (List.map
                                              (fun cnts =>
                                                 match cnts with (cn,ts) =>
                                                                 (cn,(tvs,List.map (type_name_subst tenvT) ts, id))
                                                 end)
                                              ctors)))
  | _,_ => []
  end.

(* For the value restriction on let-based polymorphism *)
Print exp.
Fixpoint is_value (e : exp) : bool :=
  match e with
  | ECon _ es => forallb is_value es
  | EVar _ => true
  | EFun _ _ => true
  | ELannot e' _ => is_value e'
  | _ => false
  end.

Inductive type_p : nat -> type_env -> pat -> t -> list (tvarN * t) -> Prop :=
| MatchPvar : forall tvs tenv n t,
    check_freevars tvs [] t = true -> type_p tvs tenv (Pvar n) t [(n,t)]
| MatchPconSome : forall tvs tenv cn ps ts tvs' tn ts' bindings,
    forallb (check_freevars tvs []) ts' = true ->
    List.length ts' = List.length tvs' ->
    type_ps tvs tenv ps (map (type_subst (combine tvs' ts')) ts) bindings ->
    nsLookup ident_string_dec cn (tec tenv) = Some (tvs', ts, tn) ->
    type_p tvs tenv (Pcon (Some cn) ps) (Tapp ts' tn) bindings
| MatchPconNon : forall tvs tenv ps ts bindings,
    type_ps tvs tenv ps ts bindings ->
    type_p tvs tenv (Pcon None ps) (Ttup ts) bindings
with type_ps : nat -> type_env -> list pat -> list t -> list (varN * t) -> Prop :=
| MatchEmpty : forall tvs tenv, type_ps tvs tenv [] [] []
| MatchCons : forall tvs tenv p ps t ts bindings bindings',
    type_p tvs tenv p t bindings ->
    type_ps tvs tenv ps ts bindings' ->
    type_ps tvs tenv (p::ps) (t::ts) (bindings'++bindings).

Print exp.
Print "Uniqe".
Print type_env.
Inductive type_e : type_env -> tenv_val_exp -> exp -> t -> Prop :=
| TypeEConSome : forall tenv tenvE cn es tvs tn ts' ts,
    forallb (check_freevars (num_tvs tenvE) []) ts' = true ->
    List.length tvs = List.length ts ->
    type_es tenv tenvE es (map (type_subst (combine tvs ts')) ts) ->
    nsLookup ident_string_dec cn (tec tenv) = Some (tvs, ts, tn) ->
    type_e tenv tenvE (ECon (Some cn) es) (Tapp ts' tn)
| TypeEConNone : forall tenv tenvE es ts,
    type_es tenv tenvE es ts ->
    type_e tenv tenvE (ECon None []) (Ttup ts)
| TypeEVar : forall tenv tenvE n t targs tvs,
    tvs = List.length targs ->
    forallb (check_freevars (num_tvs tenvE) []) targs = true ->
    lookup_var n tenvE tenv = Some (tvs,t) ->
    type_e tenv tenvE (EVar n) (deBruijn_subst 0 targs t)
| TypeEFun : forall tenv tenvE n e t1 t2,
    check_freevars (num_tvs tenvE) [] t1 = true ->
    type_e tenv (Bind_name n 0 t1 tenvE) e t2 ->
    type_e tenv tenvE (EFun n e) (Tfn t1 t2)
| TypeEApp : forall tenv tenvE op es ts t,
type_es tenv tenvE es ts ->
type_op op ts t = true ->
check_freevars (num_tvs tenvE) [] t = true ->
type_e tenv tenvE (EApp op es) t
| TypeEMat : forall tenv tenvE e pes t1 t2,
    type_e tenv tenvE e t1 ->
    pes <> [] ->
    (forall p e,
        (exists bindings,
          NoDup (pat_bindings p) ->
          type_p (num_tvs tenvE) tenv p t1 bindings ->
          type_e tenv (bind_var_list 0 bindings tenvE) e t2)) ->
    type_e tenv tenvE (EMat e pes) t2
| TypeELannot : forall tenv tenvE e l t,
    type_e tenv tenvE e t ->
    type_e tenv tenvE (ELannot e l) t
with type_es : type_env -> tenv_val_exp -> list exp -> list t -> Prop :=
| TypeESEmpty : forall tenv tenvE, type_es tenv tenvE [] []
| TypeESCons : forall tenv tenvE e es t ts,
    type_e tenv tenvE e t ->
    type_es tenv tenvE es ts ->
    type_es tenv tenvE (e::es) (t::ts)
with type_funs : type_env -> tenv_val_exp -> list (varN * varN * exp) -> list (varN * t) -> Prop :=
| NoFuns : forall tenv tenvE, type_funs tenv tenvE [] []
| Funs : forall tenv tenvE fn n e funs bindings t1 t2,
    check_freevars (num_tvs tenvE) [] (Tfn t1 t2) = true ->
    type_e tenv (Bind_name n 0 t1 tenvE) e t2  ->
    type_funs tenv tenvE funs bindings ->
    lookup string_dec fn bindings = None ->
    type_funs tenv tenvE ((fn, n, e)::funs) ((fn, Tfn t1 t2)::bindings).

Definition tenv_add_tvs (tvs : nat) (bindings : alist varN t) : alist varN (nat * t) :=
  map (fun nt => match nt with (n,t) => (n,(tvs,t)) end) bindings.

Definition type_pe_determ (tenv : type_env) (tenvE : tenv_val_exp) (p : pat) (e : exp) : Prop :=
  forall t1 tenv1 t2 tenv2,
    type_p 0 tenv p t1 tenv1 -> type_e tenv tenvE e t1 ->
    type_p 0 tenv p t2 tenv2 -> type_e tenv tenvE e t2 ->
    tenv1 = tenv2.

Definition tscheme_inst  (tvs_spec tvs_impl : nat) (t_spec t_impl : t) : Prop :=
  exists subst,
    List.length subst = tvs_impl ->
    check_freevars tvs_impl [] t_impl = true ->
    forallb (check_freevars tvs_spec []) subst = true ->
    deBruijn_subst 0 subst t_impl = t_spec.

Definition tenvLift mn tenv :=
  {| tev := nsLift mn (tev tenv); tec := nsLift mn (tec tenv); tet := nsLift mn (tet tenv) |}.
