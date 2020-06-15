Set Implicit Arguments.
From TLC Require Import LibLogic LibReflect.
From TLC Require LibListZ.
Require Import CakeSem.Namespace.
Require Import CakeSem.Utils.
Require Import CakeSem.CakeAST.
Require Import CakeSem.SemanticsAux.
Require Import CakeSem.ffi.FFI.
Require Import String.
Require Import List.
Import ListNotations.
Require Import ZArith.
Require String.


Open Scope string.
Open Scope Z_scope.
Open Scope list_scope.


(*--------------------------*)
(** Notes *)

(* LATER: we could use implicit types to avoid type annotations for arguments of constructors throughout the files.
   This would reduce the clutter. However, it requires renaming a bunch of variables, and would make it harder
   to keep in sync with the cakeML semantics, so let's not do it now. *)

(*--------------------------*)

(** If the flag [doTypeChecks] is True, then the semantics performs a few type checks like the CakeML semantics does.
    If the source code does type-check independently, then the flag may be set to False without altering the semantics. *)

Parameter doTypeChecks : bool.

Definition TypeCheck (P:Prop) :=
  if doTypeChecks then P else True.

(* BACKPORT: these definitions should be used throughout (with result in bool) *)

Definition UniquePatBindings (p:pat) : Prop :=
  LibList.noduplicates (pat_bindings p).

Definition UniqueRecIdent (funs : list (varN * varN * exp)) : Prop :=
  LibList.noduplicates (List.map (fun '(f,_,_) => f) funs).

Definition UniqueCtorsInDef (td : list tvarN * typeN * list (conN * list ast_t)) : Prop :=
  let '(tvs,tn,condefs) := td in
  LibList.noduplicates (List.map (fun '(n,_) => n) condefs).

Definition UniqueCtorsInDefs (tds : typeDef) : Prop :=
  LibList.Forall UniqueCtorsInDef tds.


(*--------------------------*)



(* ********************************************************************** *)
(** * Primitive operations *)

(* ---------------------------------------------------------------------- *)
(** ** Equality *)

(** [appEq v1 v2 P] asserts that the values [v1] and [v2] are comparable
    and that the proposition [P] characterizes whether they are equal.

    [appEqList vs1 vs2 P] is similar, and requires the list to be of the
    same lengths. *)

(** BACKPORT: it is very strange to specify that all closures are equal,
    this will certainly cause end-user bugs eventually. *)

Inductive appEq : val -> val -> Prop -> Prop :=

  | appEq_lit : forall l1 l2,
      TypeCheck (lit_same_type l1 l2) ->
      appEq (Litv l1) (Litv l2) (l1 = l2)

  | appEq_loc : forall l1 l2,
      appEq (Loc l1) (Loc l2) (l1 = l2)

  | appEq_closure : forall v1 v2,
      is_closure v1 ->
      is_closure v2 ->
      appEq v1 v2 True

  | appEq_conv_eq : forall cn vs1 vs2 P,
      length vs1 = length vs2 ->
      appEqList vs1 vs2 P ->
      appEq (Conv cn vs1) (Conv cn vs2) P

  | appEq_conv_neq : forall cn1 cn2 vs1 vs2,
      cn1 <> cn2 ->
      TypeCheck (ctor_same_type cn1 cn2) ->
      appEq (Conv cn1 vs1) (Conv cn2 vs2) False

  | appEq_vector_eq_length : forall vs1 vs2 P,
      length vs1 = length vs2 ->
      appEqList vs1 vs2 P ->
      appEq (Vectorv vs1) (Vectorv vs2) P

  | appEq_vector_neq_length : forall vs1 vs2,
      length vs1 <> length vs2 ->
      appEq (Vectorv vs1) (Vectorv vs2) False

with appEqList : list val -> list val -> Prop -> Prop :=

  | appEqList_nil :
      appEqList [] [] True

  | appEqList_cons : forall v1 v2 vs1 vs2 P Ps,
      appEq v1 v2 P ->
      appEqList vs1 vs2 Ps ->
      appEqList (v1::vs1) (v2::vs2) (P /\ Ps).


(* ---------------------------------------------------------------------- *)
(** ** Primitive operations *)

(** [appr s ffi op vs s' ffi' v'] asserts that the evaluation of [op] on the arguments [vs]
    produces output [v], and updates the states accordingly.
    This is an inductive version of do_app.

    DISCLAIMER: currently covers only a subset of primitive functions. *)


Inductive appR (FFI : Type) (s : store val) (t : ffi_state FFI) : op -> list val -> store val -> ffi_state FFI -> val -> Prop :=

  | appR_Opn : forall op (a b : int),
      ((op = Divide \/ op = Modulo) -> b <> 0) ->
      appR s t (Opn op) [Litv (IntLit a); Litv (IntLit b)] s t (Litv (IntLit (opn_lookup op a b)))

  | appR_Opb : forall op (a b : int),
      appR s t (Opb op) [Litv (IntLit a); Litv (IntLit b)] s t (Propv (opb_lookup_Prop op a b))

  | appR_Equality : forall (v1 v2 : val) (P:Prop),
      appEq v1 v2 P ->
      appR s t Equality [v1; v2] s t (Propv P)

  | appR_Opassign : forall s' v lnum,
      s' = store_assign_nocheck lnum (Refv v) s ->
      appR s t Opassign [Loc lnum; v] s' t ConvUnit

  | appR_Opref : forall s' v n,
      (s',n) = store_alloc (Refv v) s ->
      appR s t Opref [v] s' t (Loc n)

  | appR_Opderef : forall v n,
      store_lookup n s = Some (Refv v) ->
      appR s t Opderef [Loc n] s t v

  | appR_Aalloc : forall n v s' lnum n',
      n >= 0 ->
      n = Z.of_nat n' ->
      (s',lnum) = store_alloc (Varray (List_replicate n' v)) s ->
      appR s t Aalloc [Litv (IntLit n); v] s' t (Loc lnum)

  | appR_Alength : forall n ws,
      store_lookup n s = Some (Varray ws) ->
      appR s t Alength [Loc n] s t (Litv (IntLit (Z.of_nat (List.length ws))))

  | appR_Asub : forall lnum i vs v i',
      store_lookup lnum s = Some (Varray vs) ->
      (0 <= i < Zlength vs) ->
      i = Z.of_nat i' ->
      v = LibList.nth i' vs ->
      appR s t Asub [Loc lnum; Litv (IntLit i)] s t v

  | appR_Aupdate : forall lnum i n (vs:list val) s' v i',
      store_lookup n s = Some (Varray vs) ->
      (0 <= i < Zlength vs)%Z ->
      i = Z.of_nat i' ->
      s' = store_assign_nocheck lnum (Varray (LibList.update i' v vs)) s ->
      appR s t Aupdate [Loc lnum; Litv (IntLit i); v] s' t ConvUnit.

(** Alternative definitions using LibListZ to manipulate lists using integer indices directly

  | appR_Aalloc' : forall n v s' lnum,
      n >= 0 ->
      (s',lnum) = store_alloc (Varray (ListZ_replicate n v)) s ->
      appR s t Aalloc [Litv (IntLit n); v] s' t (Loc lnum)

  | appR_Alength' : forall n ws,
      store_lookup n s = Some (Varray ws) ->
      appR s t Alength [Loc n] s t (Litv (IntLit (LibListZ.length ws)))

  | appR_Asub' : forall lnum i vs,
      store_lookup lnum s = Some (Varray vs) ->
      (0 <= i < List.length vs)%Z ->
      appR s t Asub [Loc lnum; Litv (IntLit i)] s t (LibContainer.read vs i)

  | appR_Aupdate' : forall lnum i n vs s' v,
      store_lookup n s = Some (Varray vs) ->
      (0 <= i < List.length vs)%Z ->
      s' = store_assign_nocheck lnum (Varray (LibContainer.update vs i v)) s ->
      appR s t Aupdate [Loc lnum; Litv (IntLit i); v] s' t ConvUnit.
*)

(* ---------------------------------------------------------------------- *)
(** ** Regular function calls *)

(** [opapp v env n e] asserts that [v] is a closure or recursive closure
    whose argument is named [n] and whose body is [e], to be executed in
    an environment [env] that includes the recursive bindings (if any).
    This is an inductive version of [do_opapp] *)

Inductive opapp : val -> sem_env val -> varN -> exp -> Prop :=

  | opapp_Closure : forall (env : sem_env val) (n : varN) (e : exp),
      opapp (Closure env n e) env n e

  | opapp_Recclosure : forall (env env': sem_env val) (funs : list (varN * varN * exp)) (nfun n : varN) (e : exp),
      TypeCheck (UniqueRecIdent funs) ->
      env' = update_sev env (build_rec_env funs env (sev env)) ->
      find_recfun nfun funs = Some (n,e) ->
      opapp (Recclosure env funs nfun) env' n e.


(* ********************************************************************** *)
(** * Pattern matching *)

(* ---------------------------------------------------------------------- *)
(** ** Matching against one pattern *)

(** [pmatchR cenv st p v r] matches a value [v] against a pattern [p] and relates it
    to a result [r] which is either [No_match] or [Match env_v] for some set of bindings [env_v].

    Note: for tuples and constructors, the assumption [length vs = length ps] is redundant
    with [patchlistR ... ps vs]  *)

Inductive pmatchR (cenv : env_ctor) : store val -> pat -> val -> match_result (alist varN val) -> Prop :=

  | pmatchR_Pany : forall (sto : store val) (v : val),
      pmatchR cenv sto Pany v (Match [])

  | pmatchR_Pvar : forall (sto : store val) (v : val) (x : varN),
      pmatchR cenv sto (Pvar x) v (Match [(x,v)])

  | pmatchR_Plit_yes : forall (sto : store val) (l : lit),
      pmatchR cenv sto (Plit l) (Litv l) (Match [])

  | pmatchR_Plit_no : forall (sto : store val) (l1 l2 : lit),
      TypeCheck (lit_same_type l1 l2) ->
      l1 <> l2 ->
      pmatchR cenv sto (Plit l1) (Litv l2) No_match

  | pmatchR_Ptuple : forall (sto : store val) (ps : list pat) (vs : list val) m,
      pmatchListR cenv sto ps vs m ->
      pmatchR cenv sto (Pcon None ps) (Conv None vs) m

  | pmatchR_PconYes : forall (sto : store val) (n : ident modN conN) (nstamp : stamp) (ps : list pat) (vs : list val) m,
      nsLookup n cenv = Some (length ps, nstamp) ->
      pmatchListR cenv sto ps vs m ->
      pmatchR cenv sto (Pcon (Some n) ps) (Conv (Some nstamp) vs) m

  | pmatchR_PconNo : forall (sto : store val) (n : ident modN conN) (nstamp1 nstamp2 : stamp) (ps : list pat) (vs : list val),
      nsLookup n cenv = Some (length ps, nstamp2) ->
      TypeCheck (stamp_same_type nstamp1 nstamp2) ->
      nstamp1 <> nstamp2 ->
      pmatchR cenv sto (Pcon (Some n) ps) (Conv (Some nstamp1) vs) No_match

  | pmatchR_Pref : forall (sto : store val) (lnum : nat) (p : pat) (v : val) m,
     store_lookup lnum sto = Some (Refv v) ->
     pmatchR cenv sto p v m ->
     pmatchR cenv sto (Pref p) (Loc lnum) m

  | pmatchR_Ptannot : forall (sto : store val) (p : pat) (v : val) (t : ast_t) m,
      pmatchR cenv sto p v m ->
      pmatchR cenv sto (Ptannot p t) v m

(** [pmatchListR cenv st ps vs r] matches a list of values [vs] against a list of patterns [ps],
    and relates it to a result [r] which is either [No_match] or [Match env_v] for some set of
    bindings [env_v].
    The predicate can only hold when [ps] and [vs] have the same length. *)

with pmatchListR (cenv: env_ctor) : store val -> list pat -> list val -> match_result (alist varN val) -> Prop :=

  | pmatchListR_nil : forall (sto : store val),
      pmatchListR cenv sto [] [] (Match [])

  | pmatchListR_cons_yes : forall (sto : store val) (p : pat) (ps : list pat) (v : val) (vs : list val) env_v1 env_v2,
      pmatchR cenv sto p v (Match env_v1) ->
      pmatchListR cenv sto ps vs (Match env_v2) ->
      pmatchListR cenv sto (p::ps) (v::vs) (Match (env_v1 ++ env_v2))
      (* Note: the order of nsAppend should be irrelevant because pattern variables are unique. *)

  | pmatchListR_cons_no : forall (sto : store val) (p : pat) (ps : list pat) (v : val) (vs : list val) m,
      pmatchR cenv sto p v No_match ->
      pmatchListR cenv sto ps vs m ->
      pmatchListR cenv sto (p::ps) (v::vs) No_match.


(* ---------------------------------------------------------------------- *)
(** ** Matching against a list of clauses *)

(** [matR st env v pes matchres] matches the value [v] against the list of clauses [pes],
    and returns [None] if no pattern matches, or [Some (env_v,e_clause)] if the first clause that
    applies has body [e_clause] and instantiate the pattern variables according to [env_v].
    This is an inductive version of [evaluate_match] from the Lem semantics, up to the fact that
    it does not perform the recursive call to evaluate directly, but instead returns the arguments
    to be provided for that call. *)
(* Inductive matR : (A : Type) (st : state A) (env : sem_env val): val -> pat * exp -> option (alist varN val * exp) := *)
(* | matR_yes : forall (v : val) (p : pat) (e : exp) env_v, *)
(*     pmatchR (sec env) (refs st) p v (Match env_v) -> *)
(*     matR st env v (p,e) (Some (env_v,e)) *)

(* | matR_no : forall (v : val) (p : pat) (e : exp), *)
(*     pmatchR (sec env) (refs st) p v No_match -> *)
(*     matR st env v (p,e) None *)

(* with matRList (A : Type) (st : state A) (env : sem_env val) : val -> list (pat * exp) -> option (alist varN val * exp) -> Prop := *)

(*    | matRList_nil : forall (v : val), *)
(*       matRList st env v [] None *)

(*    | matRList_consYes : forall (v : val) (p : pat) (e : exp) (pes' : list (pat * exp)) env_v, *)
(*        TypeCheck (UniquePatBindings p) -> *)
(*        pmatchR (sec env) (refs st) p v (Match env) -> *)
(*        matRList st env v ((p,e)::pes') (Some (env_v,e)). *)

 Inductive matR (A : Type) (st : state A) (env : sem_env val) : val -> list (pat * exp) -> option (alist varN val * exp) -> Prop :=
 | matR_nil : forall (v : val),
     matR st env v [] None

 | matR_consFail : forall (v : val) (p : pat) (e : exp) (pes' : list (pat * exp)),
       TypeCheck (UniquePatBindings p) ->
       pmatchR (sec env) (refs st) p v No_match ->
       matR st env v (pes') None ->
       matR st env v ((p,e)::pes') None

 | matR_consSucc : forall (v : val) (p : pat) (e e' : exp) (pes' : list (pat * exp)) env_v,
     TypeCheck (UniquePatBindings p) ->
     (pmatchR (sec env) (refs st) p v (Match env_v) /\ e = e') \/ matR st env v pes' (Some (env_v,e')) ->
     matR st env v ((p,e)::pes') (Some (env_v,e')).


(* ********************************************************************** *)
(** * Evaluation *)

(* ---------------------------------------------------------------------- *)
(** ** Evaluation of expressions *)

(** [expR st env e (st', Rval v)] asserts that, in environment [env], the expression [e] evaluates to [v],
    and updates the state from [st] to [st']. *)

Inductive expR (A : Type) (st : state A) (env : sem_env val) : exp -> (state A) * result val val -> Prop :=

  | expR_ELit : forall (l : lit),
      expR st env (ELit l) (st, Rval (Litv l))

  | expR_ECon : forall (st' : state A) (es : list exp) (vs : list val) (o : constr_id) (os : option stamp),
      TypeCheck (con_check (sec env) o (length es)) ->
      expListRevR st env es (st', Rval vs) ->
      con_build (sec env) o os ->
      expR st env (ECon o es) (st', Rval (Conv os vs))

  | expR_EVar : forall (v : val) (i : ident modN varN),
      nsLookup i (sev env) = Some v ->
      expR st env (EVar i) (st, Rval v)

  | expR_EFun : forall (e : exp) (x : varN),
      expR st env (EFun x e) (st, Rval (Closure env x e))

  | expR_EAppFunction  : forall (st': state A) (env' envclos : sem_env val) (ebody : exp) (es : list exp) (n : varN) v vclos res,
      expListRevR st env es (st', Rval [vclos; v]) ->
      opapp vclos envclos n ebody ->
      env' = update_sev envclos (nsBind n v (sev envclos)) ->
      expR st' env' ebody res ->
      expR st env (EApp Opapp es) res

  | expR_EAppPrimitive : forall (st' st'' : state A) (s' : store val) (ffi' : ffi_state A) (o : op) (es : list exp) (v : val) (vs : list val),
      o <> Opapp -> (* redundant with [appR] but perhaps convenient in proofs *)
      expListRevR st env es (st', Rval vs) ->
      appR (refs st') (ffi st') o vs s' ffi' v ->
      st'' = state_update_refs_and_ffi st' s' ffi' ->
      expR st env (EApp o es) (st'', Rval v)

  | expR_ELogFst : forall (st' : state A) (op : lop) (e1 e2 : exp) (v1: val),
      expR st env e1 (st', Rval v1) ->
      (match op with
       | And => v1 = Boolv false
       | Or => v1 = Boolv true
       end) ->
      expR st env (ELog op e1 e2) (st', Rval v1)

  | expR_ELogSnd : forall (st' : state A) (op : lop) (e1 e2 : exp) (v1: val) res,
      expR st env e1 (st', Rval v1) ->
      (match op with
       | And => v1 = Boolv true
       | Or => v1 = Boolv false
       end) ->
      expR st' env e2 res ->
      expR st env (ELog op e1 e2) res

  | expR_EIf : forall (st' : state A) (e1 e2 e3 : exp) v1 res,
      expR st env e1 (st', Rval v1) ->
      (v1 = Boolv true  -> expR st' env e2 res) ->
      (v1 = Boolv false -> expR st' env e3 res) ->
      expR st env (EIf e1 e2 e3) res

  | expR_EMatVal : forall (env' : sem_env val) (e : exp) (pes : list (pat * exp)) (v : val) st' env_v e_clause res,
      expR st env e (st', Rval v) ->
      matR st env v pes (Some (env_v, e_clause)) ->
      env' = update_sev env (nsAppend (alist_to_ns env_v) (sev env)) ->
      expR st env' e_clause res ->
      expR st env (EMat e pes) res

  | expR_ELet : forall (st' : state A) (env' : sem_env val) (e1 e2 : exp) (v1 : val) (o : option varN) res,
      expR st env e1 (st', Rval v1) ->
      env' = update_sev env (nsOptBind o v1 (sev env)) ->
      expR st' env' e2 res ->
      expR st env (ELet o e1 e2) res

  | expR_ELetrec : forall (env': sem_env val) (e : exp) (funs : list (varN * varN * exp)) res,
      env' = update_sev env (build_rec_env funs env (sev env)) ->
      expR st env' e res ->
      expR st env (ELetrec funs e) res

  | expR_ETannot : forall (e : exp) (t : ast_t) res,
      expR st env e res ->
      expR st env (ETannot e t) res

  | expR_ELannot : forall (e : exp) (l : locs) res,
      expR st env e res ->
      expR st env (ELannot e l) res


(* [expListRevR st env es (st', Rval vs)] asserts that the expressions [es] evaluate to the list of values [vs]
   when evaluated in right-to-left order (mimics the [reverse es] and [reverse vs] from the Lem semantics),
   updating the state from [st] to [st']. *)

with expListRevR (A :Type) (st : state A) (env : sem_env val) : list exp -> ((state A) * result (list val) val) -> Prop :=

   | expListRevR_nil :
       expListRevR st env [] (st, Rval [])

   | expListRevR_cons : forall (st' st'' : state A) (e : exp) (v : val) (es : list exp) (vs : list val),
       expListRevR st env es (st', Rval vs) ->
       expR st' env e (st'', Rval v) ->
       expListRevR st env (e::es) (st'', Rval (v::vs)).


(* ---------------------------------------------------------------------- *)
(** ** Evaluation of top-level declarations *)


Inductive decR (A : Type) (st : state A) (env : sem_env val) : dec -> (state A) * (result (sem_env val) val) -> Prop :=

  | decR_Dlet : forall (st' : state A) env_v env' (l : locs) (p : pat) (e : exp) (v : val),
      TypeCheck (UniquePatBindings p) ->
      expR st env e (st', Rval v) ->
      pmatchR (sec env) (refs st') p v (Match env_v) ->
      env' = {| sev := alist_to_ns env_v; sec := nsEmpty |} ->
      decR st env (Dlet l p e) (st', Rval env')

  | decR_Dletrec : forall (env' : sem_env val) (l : locs) (funs : list (varN * varN * exp)),
      TypeCheck (UniqueRecIdent funs) ->
      env' = {| sev := build_rec_env funs env nsEmpty ; sec := nsEmpty |} ->
      decR st env (Dletrec l funs) (st, Rval env')

  | decR_Dtype : forall (env' : sem_env val) (st' : state A) (l : locs) (tds : typeDef),
      TypeCheck (UniqueCtorsInDefs tds) ->
      st' = state_update_next_type_stamp st (next_type_stamp st + length tds) ->
      env' = {| sev := nsEmpty ; sec := build_tdefs (next_type_stamp st) tds |} ->
      decR st env (Dtype l tds) (st', Rval env')

  | decR_Dtabbrev : forall (loc : locs) (tvs : list tvarN) (tn : typeN) (t : ast_t),
      decR st env (Dtabbrev loc tvs tn t) (st, Rval empty_sem_env)

  | decR_Dexn : forall (st' : state A) env' (loc : locs) (cn : conN) (ts : list ast_t),
      st' = state_update_next_exn_stamp st (next_exn_stamp st + 1) ->
      env' = {| sev := nsEmpty; sec := nsSing cn (length ts, ExnStamp (next_exn_stamp st)) |} ->
      decR st env (Dexn loc cn ts) (st', Rval env')

  | decR_Dmod : forall (st' : state A) (env' env'' : sem_env val) (mn : modN) (ds : list dec),
      decListR st env ds (st', Rval env') ->
      env'' = {| sev := nsLift mn (sev env'); sec := nsLift mn (sec env') |} ->
      decR st env (Dmod mn ds) (st', Rval env'')

  | decR_Dlocal : forall (st' : state A) (env' : sem_env val) (lds ds : list dec) res,
      decListR st env lds (st', Rval env') ->
      decListR st' (extend_dec_env env' env) ds res ->
      decR st env (Dlocal lds ds) res

with decListR (A : Type) (st : state A) (env : sem_env val) : list dec -> (state A) * (result (sem_env val) val) -> Prop :=

  | decR_Dnil :
      decListR st env [] (st, Rval empty_sem_env)

  | decR_DconsRval : forall (st' st'' : state A) (env1 env2 : sem_env val) (d : dec) (ds : list dec),
      decR st env d (st', Rval env1) ->
      decListR st' (extend_dec_env env1 env) ds (st'', Rval env2) ->
      decListR st env (d::ds) (st'', Rval (extend_dec_env env2 env1)).


(* ********************************************************************** *)
(** * Notes for future work *)

(*--------------------------------------------------------------
  LATER: treatment of exceptions and the propagation of exceptions

  | ERaise_R  : forall (st': state A) (e : exp) (v :val),
      expR st env e (st', Rval v) ->
      expR st env (ERaise e) (st', Rerr (Rraise v))
      expR st env e (st', Rerr (Rraise err_v)) ->
      matR st' env err_v l err_v (st'', r) ->
      expR st env (EHandle e l) (st'', r)

   | ArgsFail : forall (st' st'': state A) (res_val : result (list val) val) (err : error_result val) (e : exp) (es : list exp),
       expListRevR st env es (st', res_val) -> expR st' env e (st'', Rerr err) ->
       expListRevR st env (e::es) (st'', Rerr err)
   | ArgsPrevFail : forall (st' st'' : state A) (e : exp) (v : val) (es : list exp) (err : error_result val),
       expListRevR st env es (st', Rerr err) -> expListRevR st env (e::es) (st', Rerr err)
  | DconsRerr_R : forall (st' : state A) (d : dec) (ds : list dec) (res : result (sem_env val) val) (err_v : error_result val),
      decR st env d (st', res) ->
      combineDecResultR env res (Rerr err_v) ->
      decListR st env (d::ds) (st', Rerr err_v).

  | EMatVal_R : forall (env' : sem_env val) (e : exp) (pes : list (pat * exp)) (v : val) st' res,
      expR st env e (st', Rval v) ->
      matR st env v pes matchres ->
      (match matchres with
      | None -> res = (st, Rerr (Rraise bind_exn_v))
      | Some (env_clause, e_clause) ->
          let env' := extend_dec_env env_clause env in
          ---non strictly positive occurence here, so need to eliminate the match---
          expR st env' e_clause res
      end) ->
      expR st env (EMat e pes) res

  + fallthrough for every rule
    or a factorized fallthrough using pretty-big-step presentation

  | decR_Dmod_Fail : forall (st' : state A) (mn : modN) (ds : list dec) (d : list dec) (err_v : error_result val),
      decListR st env ds (st', Rerr err_v) ->
      decR st env (Dmod mn ds) (st', Rerr err_v)

  | decR_DletExpFail : forall (st' st'' : state A) (env' : sem_env val) (sto : store val) (l : locs)
                      (p : pat) (e : exp) (err_v : error_result val) (res : result (sem_env val) val),
      expR st env e (st', Rerr err_v) ->
      decR st env (Dlet l p e) (st', Rerr err_v)

  | decR_DletMatFail : forall (st' st'' : state A) (env' : sem_env val) (sto : store val) (l : locs)
                      (p : pat) (e : exp) (v : val) (res : result (sem_env val) val),
      expR st env e (st', Rval v) ->
      sto = refs st' ->
      pmatchR sto env p v No_match ->
      decR st env (Dlet l p e) (st', res)


  Inductive combineDecResultR (env : sem_env val) : result (sem_env val) val -> result (sem_env val) val -> Prop :=
    | combineRerr : forall (e : error_result val),
        combineDecResultR env (Rerr e) (Rerr e)
    | combineRval : forall (env' : sem_env val),
        combineDecResultR env (Rval env') (Rval {| sev := nsAppend (sev env') (sev env);
                                                   sec := nsAppend (sec env') (sec env) |}).


FUTURE WORK vectors

   | app_VfromList : forall s t v vs,
      v_to_list v = Some vs ->
      appR s t VfromList [v] s t (Vectorv vs)


    | (Vsub, [Vectorv vs; Litv (IntLit i)]) ->
        if i < 0 then
          Just ((s,t), Rerr (Rraise sub_exn_v))
        else
          let n = natFromInteger i in
            if n >= List.length vs then
              Just ((s,t), Rerr (Rraise sub_exn_v))
            else
              Just ((s,t), Rval (List_extra.nth vs n))
    | (Vlength, [Vectorv vs]) ->
        Just ((s,t), Rval (Litv (IntLit (integerFromNat (List.length vs)))))


FUTURE WORK more on arrays

  | app_AallocEmpty : forall s t n v s' lnum,
      (s',lnum) = store_alloc (Varray []) s ->
      appR s t AallocEmpty [ConvUnit) s' t (Loc lnum)

*)


(** QUESTION: would it make sense that the recursive closures store as environment not [env]
    but directly [env with v = build_rec_env funs env env.v], rather than rebuilding
    this extended environment each time? *)
