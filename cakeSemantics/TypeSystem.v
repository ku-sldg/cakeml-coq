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
Require Import Lists.ListSet.

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
Inductive check_freevars (dbmax : nat) (tvs : list tvarN) : t -> Prop :=
| CheckTvar : forall (tv : varN),
    In tv tvs ->
    check_freevars dbmax tvs (Tvar tv)
| CheckTvar_db : forall (n : nat),
    n < dbmax -> check_freevars dbmax tvs (Tvar_db n)
| CheckTapp : forall (ts : list t) (tn : type_ident),
    Forall (check_freevars dbmax tvs) ts ->
    check_freevars dbmax tvs (Tapp ts tn).

Inductive check_freevars_ast (tvs : list tvarN) : ast_t -> Prop :=
| CheckAtapp : forall (ts : list ast_t) (tn : ident modN typeN),
    Forall (check_freevars_ast tvs) ts ->
    check_freevars_ast tvs (Atapp ts tn).

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

Definition empty_type_env :=
  mktype_env nsEmpty nsEmpty nsEmpty.

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
Inductive type_op : op -> list t -> t -> Prop :=
| TypeOpOpapp : forall ty t1 t2,
    t1 = Tfn t2 ty ->
    type_op Opapp [t1;t2] ty.

Inductive check_type_names (tenvT : tenv_abbrev) : ast_t -> Prop :=
| CTNAtapp : forall ts tn tvs t',
    nsLookup ident_string_dec tn tenvT = Some (tvs,t') ->
    List.length tvs = List.length ts ->
    check_type_names tenvT (Atapp ts tn).

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
Inductive check_ctor_tenv (tenvT : tenv_abbrev) :
  list (list tvarN * typeN * list (conN * list ast_t)) -> Prop :=
| CheckCtorTenvEmpty : check_ctor_tenv tenvT []
| CheckCtorTenvCons : forall tvs tn ctors tds,
    UniqueCtorsInDef (tvs,tn,ctors) ->
    NoDup tvs ->
    Forall (fun '(cn,ts) =>
              Forall (check_freevars_ast tvs) ts /\
              Forall (check_type_names tenvT) ts) ctors ->
    not (In tn (map (fun '(_,tn,_) => tn) tds)) ->
    check_ctor_tenv tenvT tds ->
    check_ctor_tenv tenvT ((tvs,tn,ctors)::tds).

Fixpoint build_ctor_tenv (tenvT : tenv_abbrev) (tds : list (list tvarN * typeN * list (conN * list ast_t))) (ids : list nat)
  : tenv_ctor :=
  match tds, ids with
  | [], [] => []
  | (tvs,tn,ctors)::tds', id::ids' =>
    nsAppend
      (build_ctor_tenv tenvT tds' ids')
      (alist_to_ns
         (rev
            (List.map
               (fun '(cn,ts) => (cn,(tvs,List.map (type_name_subst tenvT) ts, id)))
               ctors)))
  | _,_ => []
  end.

(* For the value restriction on let-based polymorphism *)
Inductive is_value : exp -> Prop :=
| IsValueECon : forall es o, Forall is_value es -> is_value (ECon o es)
| IsValueEVar : forall id, is_value (EVar id)
| IsValueEFun : forall nm e, is_value (EFun nm e)
| IsValueELannot : forall e l, is_value e -> is_value (ELannot e l).

Inductive type_p : nat -> type_env -> pat -> t -> list (tvarN * t) -> Prop :=
| MatchPvar : forall tvs tenv n ty,
    check_freevars tvs [] ty -> type_p tvs tenv (Pvar n) ty [(n,ty)]
| MatchPconSome : forall tvs tenv cn ps ts tvs' tn ts' bindings,
    Forall (check_freevars tvs []) ts' ->
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

Inductive type_e : type_env -> tenv_val_exp -> exp -> t -> Prop :=
| TypeEConSome : forall tenv tenvE cn es tvs tn ts' ts,
    Forall (check_freevars (num_tvs tenvE) []) ts' ->
    List.length tvs = List.length ts ->
    type_es tenv tenvE es (map (type_subst (combine tvs ts')) ts) ->
    nsLookup ident_string_dec cn (tec tenv) = Some (tvs, ts, tn) ->
    type_e tenv tenvE (ECon (Some cn) es) (Tapp ts' tn)
| TypeEConNone : forall tenv tenvE es ts,
    type_es tenv tenvE es ts ->
    type_e tenv tenvE (ECon None []) (Ttup ts)
| TypeEVar : forall tenv tenvE n t targs tvs,
    tvs = List.length targs ->
    Forall (check_freevars (num_tvs tenvE) []) targs ->
    lookup_var n tenvE tenv = Some (tvs,t) ->
    type_e tenv tenvE (EVar n) (deBruijn_subst 0 targs t)
| TypeEFun : forall tenv tenvE n e t1 t2,
    check_freevars (num_tvs tenvE) [] t1 ->
    type_e tenv (Bind_name n 0 t1 tenvE) e t2 ->
    type_e tenv tenvE (EFun n e) (Tfn t1 t2)
| TypeEApp : forall tenv tenvE op es ts t,
    type_es tenv tenvE es ts ->
    type_op op ts t ->
    check_freevars (num_tvs tenvE) [] t ->
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
    check_freevars (num_tvs tenvE) [] (Tfn t1 t2) ->
    type_e tenv (Bind_name n 0 t1 tenvE) e t2  ->
    type_funs tenv tenvE funs bindings ->
    lookup string_dec fn bindings = None ->
    type_funs tenv tenvE ((fn, n, e)::funs) ((fn, Tfn t1 t2)::bindings).

Definition tenv_add_tvs (tvs : nat) (bindings : alist varN t) : alist varN (nat * t) :=
  map (fun '(n,t) => (n,(tvs,t))) bindings.

Definition type_pe_determ (tenv : type_env) (tenvE : tenv_val_exp) (p : pat) (e : exp) : Prop :=
  forall t1 tenv1 t2 tenv2,
    type_p 0 tenv p t1 tenv1 -> type_e tenv tenvE e t1 ->
    type_p 0 tenv p t2 tenv2 -> type_e tenv tenvE e t2 ->
    tenv1 = tenv2.

Definition tscheme_inst (spec impl : nat * t) : Prop :=
  match spec,impl with
  | (tvs_spec, t_spec), (tvs_impl, t_impl) =>
    exists subst,
    List.length subst = tvs_impl ->
    check_freevars tvs_impl [] t_impl ->
    Forall (check_freevars tvs_spec []) subst ->
    deBruijn_subst 0 subst t_impl = t_spec
  end.

Definition tenvLift mn tenv :=
  {| tev := nsLift mn (tev tenv); tec := nsLift mn (tec tenv); tet := nsLift mn (tet tenv) |}.

Definition setFromList (A : Type) (dec : forall (x y : A), {x=y} + {x<>y}) (l : list A) :=
  set_union dec [] l.

Fixpoint map2 {A B C : Type} (f : A -> B -> C) (l1 : list A) (l2 : list B) : list C :=
  match l1, l2 with
  | [], [] => []
  | _, [] => []
  | [], _ => []
  | a::l1',b::l2' => (f a b)::(map2 f l1' l2')
  end.

Definition disjoint {A : Type} (dec : forall (x y : A), {x=y}+{x<>y}) (l1 l2 : set A) : Prop :=
  Forall (fun x => not (In x l2)) l1.

Inductive type_d : bool -> type_env -> dec -> set nat -> type_env -> Prop :=
| TypeDletPoly : forall extra_checks tvs tenv p e t bindings locs,
    is_value e ->
    NoDup (pat_bindings p) ->
    type_p tvs tenv p t bindings ->
    type_e tenv (bind_tvar tvs Empty) e t ->
    (extra_checks = true ->
     forall tvs' bindings' t',
       type_p tvs' tenv p t' bindings' ->
       type_e tenv (bind_tvar tvs' Empty) e t' ->
       Forall2 tscheme_inst (List.map snd (tenv_add_tvs tvs' bindings')) (List.map snd (tenv_add_tvs tvs bindings))) ->
    type_d extra_checks tenv (Dlet locs p e) []
           {| tev := alist_to_ns (tenv_add_tvs tvs bindings); tec := nsEmpty; tet := nsEmpty |}

| TypeDletMono : forall extra_checks tenv p e t bindings locs,
    (* The following line makes sure that when the value restriction prohibits
   generalisation, a type error is given rather than picking an arbitrary
   instantiation. However, we should only do the check when the extra_checks
   argument tells us to. *)
    extra_checks = true -> not (is_value e) ->
    type_pe_determ tenv Empty p e ->
    NoDup (pat_bindings p) ->
    type_p 0 tenv p t bindings ->
    type_e tenv Empty e t ->
    type_d extra_checks tenv (Dlet locs p e)
           [] {| tev := alist_to_ns (tenv_add_tvs 0 bindings); tec := nsEmpty; tet := nsEmpty |}
| TypeDletrec : forall extra_checks tenv funs bindings tvs locs,
    type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs Empty)) funs bindings ->
    (extra_checks = true ->
     forall tvs' bindings',
       type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs' Empty)) funs bindings' ->
       Forall2 tscheme_inst (List.map snd (tenv_add_tvs tvs' bindings')) (List.map snd (tenv_add_tvs tvs bindings))) ->
    type_d extra_checks tenv (Dletrec locs funs)
           [] {| tev := alist_to_ns (tenv_add_tvs tvs bindings); tec := nsEmpty; tet := nsEmpty |}
| TypeDtype : forall extra_checks tenv tdefs type_identities tenvT locs,
    NoDup type_identities ->
    disjoint Nat.eq_dec (setFromList nat Nat.eq_dec type_identities)
             (setFromList nat Nat.eq_dec (Tlist_num :: Tbool_num :: prim_type_nums)) ->
    check_ctor_tenv (nsAppend tenvT (tet tenv)) tdefs ->
    List.length type_identities = List.length tdefs ->
    tenvT = alist_to_ns (map2
                           (fun '(tvs,tn,ctors) i => (tn, (tvs, Tapp (List.map Tvar tvs) i)))
                           tdefs type_identities) ->
    type_d extra_checks tenv (Dtype locs tdefs)
           (setFromList nat Nat.eq_dec type_identities)
           {| tev := nsEmpty; tec := build_ctor_tenv (nsAppend tenvT (tet tenv)) tdefs type_identities; tet := tenvT |}
with type_ds : bool -> type_env -> list dec -> set nat -> type_env -> Prop :=
| TypeDSEmpty : forall extra_checks tenv,
    type_ds extra_checks tenv []
            []
            {| tev := nsEmpty; tec := nsEmpty; tet := nsEmpty |}
| TypeDSCons : forall extra_checks tenv d ds tenv1 tenv2 decls1 decls2,
    type_d extra_checks tenv d decls1 tenv1 ->
    type_ds extra_checks (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 ->
    disjoint Nat.eq_dec decls1 decls2 ->
    type_ds extra_checks tenv (d::ds)
            (set_union Nat.eq_dec decls1 decls2) (extend_dec_tenv tenv2 tenv1).

(* Definition tscheme_inst2 _ ts1 ts2 := tscheme_inst ts1 ts2. *)

(* val weak_tenv : type_env -> type_env -> bool *)
(* Definition weak_tenv tenv_impl tenv_spec := *)
(*   nsSub tscheme_inst2 tenv_spec.v tenv_impl.v -> *)
(*   nsSub (fun _ x y -> x = y) (tec tenv_spec) (tec tenv_impl) *)
