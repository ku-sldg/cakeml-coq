Set Implicit Arguments.
From TLC Require Import LibLogic LibReflect.
Require Import CakeSem.Namespace.
Require Import CakeSem.Utils.
Require Import CakeSem.CakeAST.
Require Import CakeSem.SemanticPrimitives.
Require Import CakeSem.ffi.FFI.
Require Import String.
Require Import List.
Import ListNotations.
Require Import ZArith.
Require String.

Open Scope string.
Open Scope Z_scope.
Open Scope list_scope.

Definition trueConv  := Conv (Some (TypeStamp "True"  bool_type_num)) [].
Definition falseConv := Conv (Some (TypeStamp "False" bool_type_num)) [].

(*--------------------------*)
(** Notes *)

(* LATER: we could use implicit types to avoid type annotations for arguments of constructors throughout the files. *)

(* LATER: in opapp, the predicate checks for non-duplicate bindings in the closure, although this could 
    be trivially maintained as an invariant of the store throughout the execution if rec defs
    are checked at definition time. *)

(* LATER: try to make result carry not a list of values but a single value, and make argR take a continuation from list val to val. *)

(*--------------------------*)

(** [appr s ffi op vs s' ffi' v'] asserts that the evaluation of [op] on the arguments [vs] 
    produces output [v], and updates the states accordingly. *)

(** SOON [appR] will be fixed in subsequent commit *)

Inductive appR (A FFI : Type) (s : store A) (t : ffi_state FFI) : op -> list val -> store A -> ffi_state FFI -> val -> Prop :=
  | app_OpnPlus : forall (a b : int), 
      appR s t (Opn Plus) [Litv (IntLit a); Litv (IntLit b)] s t (Litv (IntLit (a + b)%Z))
  | app_OpnMinus : forall (a b : int),
      appR s t (Opn Minus) [Litv (IntLit a); Litv (IntLit b)] s t (Litv (IntLit (a - b)%Z))
  | app_OpnTimes : forall (a b : int), 
      appR s t (Opn Times) [Litv (IntLit a); Litv (IntLit b)] s t (Litv (IntLit (a * b)%Z))
  | app_OpbLtTrue  : forall (a b : int), 
      a < b -> 
      appR s t (Opb Lt) [Litv (IntLit a); Litv (IntLit b)] s t trueConv  (* could probably shorten by using boolean comparison *)
  | app_OpbLtFalse : forall (a b : int),
      not (a < b) -> (* LATER: a >= b *)
      appR s t (Opb Lt) [Litv (IntLit a); Litv (IntLit b)] s t falseConv
  | app_OpbGtTrue  : forall (a b : int), 
      a > b -> 
      appR s t (Opb Gt) [Litv (IntLit a); Litv (IntLit b)] s t trueConv
  | app_OpbGtFalse : forall (a b : int), 
      not (a > b) -> 
      appR s t (Opb Gt) [Litv (IntLit a); Litv (IntLit b)] s t falseConv
  | app_OpbLeqTrue  : forall (a b : int), 
      a <= b ->
      appR s t (Opb Leq) [Litv (IntLit a); Litv (IntLit b)] s t trueConv
  | app_OpbLeqFalse : forall (a b : int), 
      not (a <= b) -> 
      appR s t (Opb Leq) [Litv (IntLit a); Litv (IntLit b)] s t falseConv
  | app_OpbGeqTrue  : forall (a b : int), 
      a >= b -> 
      appR s t (Opb Geq) [Litv (IntLit a); Litv (IntLit b)] s t trueConv
  | app_OpbGeqFalse : forall (a b : int),
      not (a >= b) ->
      appR s t (Opb Geq) [Litv (IntLit a); Litv (IntLit b)] s t falseConv
  | app_EqualityTrue  : forall (v1 v2 : val), 
      v1 = v2 ->
      appR s t Equality [v1; v2] s t trueConv
  | app_EqualityFalse : forall (v1 v2 : val), 
      v1 <> v2 -> 
      appR s t Equality [v1; v2] s t falseConv.

(** [pmatchR cenv st p v r] matches a value [v] against a pattern [p] and relates it
    to a result [r] which is either [No_match] or [Match env_v] for some set of bindings [env_v]. *)

Inductive pmatchR : env_ctor -> store val -> pat -> val -> match_result (alist varN val) -> Prop :=

  | pmatch_Pany : forall cenv (sto : store val) (v : val), 
      pmatchR cenv sto Pany v (Match [])

  | pmatch_Pvar : forall cenv (sto : store val) (v : val) (x : varN),
      pmatchR cenv sto (Pvar x) v (Match [(x,v)])

  | pmatch_Plit_yes : forall cenv (sto : store val) (v : val) (l : lit),
      pmatchR cenv sto (Plit l) (Litv l) (Match [])

  | pmatch_Plit_no : forall cenv (sto : store val) (v : val) (l l' : lit),
      lit_same_type l l' ->
      l <> l' ->
      pmatchR cenv sto (Plit l) (Litv l') No_match

  | pmatch_Ptuple : forall cenv (sto : store val) (ps : list pat) (vs : list val) m,
      length vs = length ps -> (* redundant but convenient (?) *)
      pmatchlistR cenv sto ps vs m ->
      pmatchR cenv sto (Pcon None ps) (Conv None vs) m

  | pmatch_Pcon_yes : forall cenv (sto : store val) (n : ident modN conN) (c : conN) (nstamp : stamp) (ps : list pat) (vs : list val) m,
      nsLookup n cenv = Some (length ps, nstamp) ->
      length vs = length ps -> (* redundant but convenient (?) *)
      pmatchlistR cenv sto ps vs m -> 
      pmatchR cenv sto (Pcon (Some n) ps) (Conv (Some nstamp) vs) m

  | pmatch_Pcon_no : forall cenv (sto : store val) (n : ident modN conN) (nstamp nstamp' : stamp) (ps : list pat) (vs : list val),
      nsLookup n cenv = Some (length ps, nstamp') ->
      same_type nstamp nstamp' ->
      nstamp <> nstamp' ->
      pmatchR cenv sto (Pcon (Some n) ps) (Conv (Some nstamp) vs) No_match

  | pmatch_Pref : forall cenv (sto : store val) (lnum : nat) (p : pat) (v : val) m,
     store_lookup lnum sto = Some (Refv v) -> 
     pmatchR cenv sto p v m -> 
     pmatchR cenv sto (Pref p) (Loc lnum) m

  | pmatch_Ptannot : forall cenv (sto : store val) (p : pat) (v : val) (t : ast_t) m,
      pmatchR cenv sto p v m -> 
      pmatchR cenv sto (Ptannot p t) v m

(** [pmatchlistR cenv st ps vs r] matches a list of values [vs] against a list of patterns [ps],
    and relates it to a result [r] which is either [No_match] or [Match env_v] for some set of 
    bindings [env_v].
    The predicate can only hold when [ps] and [vs] have the same length. *)

with pmatchlistR : env_ctor -> store val -> list pat -> list val -> match_result (alist varN val) -> Prop :=

  | pmatch_empty : forall cenv (sto : store val),
      pmatchlistR cenv sto [] [] (Match [])

  | pmatch_cons_yes : forall cenv (sto : store val) (p : pat) (ps : list pat) (v : val) (vs : list val) env_v1 env_v2,
      pmatchR cenv sto p v (Match env_v1) -> 
      pmatchlistR cenv sto ps vs (Match env_v2) -> 
      pmatchlistR cenv sto (p::ps) (v::vs) (Match (env_v1 ++ env_v2))
      (* Note: the order of nsAppend should be irrelevant because pattern variables are unique. *)

  | pmatch_cons_no : forall cenv (sto : store val) (p : pat) (ps : list pat) (v : val) (vs : list val) m,
      pmatchR cenv sto p v No_match ->
      pmatchlistR cenv sto ps vs m ->
      pmatchlistR cenv sto (p::ps) (v::vs) No_match.

(** [matR st env v pes matchres] matches the value [v] against the list of clauses [pes],
    and returns [None] if no pattern matches, or [Some (env_v,e_clause)] if the first clause that
    applies has body [e_clause] and instantiate the pattern variables according to [env_v].
    This is an inductive version of [evaluate_match] from the Lem semantics, up to the fact that
    it does not perform the recursive call to evaluate directly, but instead returns the arguments
    to be provided for that call. *)

Inductive matR (A : Type) (st : state A) (env : sem_env val) : val -> list (pat * exp) -> option (alist varN val * exp) -> Prop :=

   | matR_nil : forall (v : val), 
      matR st env v [] None

   | matR_ConsMatch : forall (v : val) (p : pat) (e : exp) (pes' : list (pat * exp)) env_v,
       LibList.noduplicates (pat_bindings p) -> (* LATER: this fact could be maintained by invariants *)
       pmatchR (sec env) (refs st) p v (Match env_v) -> 
       matR st env v ((p,e)::pes') (Some (env_v,e))

   | matR_ConsNoMatch : forall (v : val) (p : pat) (e :exp) (pes' : list (pat * exp)) matchres,
       LibList.noduplicates (pat_bindings p) -> (* LATER: this fact could be maintained by invariants *)
       pmatchR (sec env) (refs st) p v No_match -> 
       matR st env v pes' matchres -> 
       matR st env v ((p,e)::pes') matchres.

(** [con_check cenv o l] asserts that the constructor (or None for a tuple) admits arity [l]. 
    (Note that tuples admit any arity.)  
    This is an inductive version of [do_con_check] *)

Inductive con_check (cenv : env_ctor) : constr_id -> nat -> Prop :=

  | con_check_none : forall l,
      con_check cenv None l

  | con_check_some : forall n l s,
      nsLookup n cenv = Some (l,s) ->
      con_check cenv (Some n) l.

(** [opapp v env n e] asserts that [v] is a closure or recursive closure
    whose argument is named [n] and whose body is [e], to be executed in 
    an environment [env] that includes the recursive bindings (if any).
    This is an inductive version of [do_opapp] *)

Inductive opapp : val -> sem_env val -> varN -> exp -> Prop :=

  | opapp_Closure : forall (env : sem_env val) (n : varN) (e : exp) (v : val),
      opapp (Closure env n e) env n e

  | opapp_Recclosure : forall (env env': sem_env val) (funs : list (varN * varN * exp)) (nfun n : varN) (e : exp) (v : val),
      LibList.noduplicates (List.map (fun '(f,_,_) => f) funs) -> (* LATER: this fact could be maintained by invariants *)
      env' = update_sev env (build_rec_env funs env (sev env)) -> 
      find_recfun nfun funs = Some (n,e) ->
      opapp (Recclosure env funs nfun) env' n e.

(** [expR st env e (st', Rval v)] asserts that, in environment [env], the expression [e] evaluates to [v],
    and updates the state from [st] to [st']. *)

Inductive expR (A : Type) (st : state A) (env : sem_env val) : exp -> (state A) * result val val -> Prop :=

  | ELit_R : forall (l : lit), 
      expR st env (ELit l) (st, Rval (Litv l))

  | EConNamed_R : forall (st' : state A) (es : list exp) (vs : list val) (o : constr_id) (i : ident modN conN) (s : stamp),
      con_check (sec env) o (length es) ->
      argR st env es (st', Rval vs) -> 
      expR st env (ECon o es) (st', Rval (Conv (Some s) vs))

  | EVar_R : forall (v : val) (i : ident modN varN),
      nsLookup i (sev env) = Some v -> 
      expR st env (EVar i) (st, Rval v)

  | EFun_R : forall (e : exp) (v : val) (x : varN),
      expR st env (EFun x e) (st, Rval (Closure env x e))

  | EAppPrimitive_R : forall (st' st'' : state A) (s s' : store val) (ffi' : ffi_state A) (o : op) (es : list exp) (v : val) (vs : list val),
      o <> Opapp -> (* redundant but convenient *)
      argR st env es (st', Rval vs) ->
      appR (refs st') (ffi st') o vs s' ffi' v ->
      st'' = state_update_refs_and_ffi st' s' ffi' ->
      expR st env (EApp o es) (st'', Rval v)

  | EAppFunction_R  : forall (st': state A) (env' envclos : sem_env val) (ebody : exp) (es : list exp) (n : varN) v vclos res,
      argR st env es (st', Rval [vclos; v]) -> 
      opapp vclos envclos n ebody ->
      env' = update_sev envclos (nsBind n v (sev envclos)) ->
      expR st' env' ebody res -> 
      expR st env (EApp Opapp es) res

  | ELogFst_R : forall (env' : sem_env val) (st' : state A) (op : lop) (e e1 e2 : exp) (v v1: val),
      expR st env e1 (st', Rval v1) -> 
      (match op with
       | And => v1 = falseConv
       | Or => v1 = trueConv
       end) ->
      expR st env (ELog op e1 e2) (st', Rval v1)

  | ELogSnd_R : forall (env' : sem_env val) (st' : state A) (op : lop) (e e1 e2 : exp) (v v1: val) res,
      expR st env e1 (st', Rval v1) -> 
      (match op with
       | And => v1 = trueConv
       | Or => v1 = falseConv
       end) ->
      expR st' env e2 res -> 
      expR st env (ELog op e1 e2) res

  | EIf_R : forall (st' : state A) (e1 e2 e3 : exp) v1 res,
      expR st env e1 (st', Rval v1) -> 
      (v1 = trueConv  -> expR st' env e2 res) -> 
      (v1 = falseConv -> expR st' env e3 res) -> 
      expR st env (EIf e1 e2 e3) res

  | EMatVal_R : forall (env' : sem_env val) (e : exp) (pes : list (pat * exp)) (v : val) st' env_v e_clause env' res,
      expR st env e (st', Rval v) -> 
      matR st env v pes (Some (env_v, e_clause)) -> 
      env' = update_sev env (nsAppend (alist_to_ns env_v) (sev env)) ->
      expR st env' e_clause res ->
      expR st env (EMat e pes) res

  | ELet_R : forall (st' : state A) (env' : sem_env val) (e1 e2 : exp) (v1 : val) (o : option varN) res,
      expR st env e1 (st', Rval v1) -> 
      env' = update_sev env (nsOptBind o v1 (sev env)) ->
      expR st' env' e2 res -> 
      expR st env (ELet o e1 e2) res

  | ELetrec_R : forall (env': sem_env val) (e : exp) (funs : list (varN * varN * exp)) res,
      env' = update_sev env (build_rec_env funs env (sev env)) -> 
      expR st env' e res -> 
      expR st env (ELetrec funs e) res

  | ETannot_R : forall (e : exp) (t : ast_t) res,
      expR st env e res -> 
      expR st env (ETannot e t) res

  | ELannot_R : forall (e : exp) (l : locs) res,
      expR st env e res -> 
      expR st env (ELannot e l) res


(* [argR st env es (st', Rval vs)] asserts that the expressions [es] evaluate to the list of values [vs]
   when evaluated in right-to-left order (mimics the [reverse es] and [reverse vs] from the Lem semantics),
   updating the state from [st] to [st']. *)

with argR (A :Type) (st : state A) (env : sem_env val) : list exp -> ((state A) * result (list val) val) -> Prop :=

   | argR_nil : 
       argR st env [] (st, Rval [])

   | argR_cons : forall (st' st'' : state A) (e : exp) (v : val) (es : list exp) (vs : list val),
       argR st env es (st', Rval vs) -> 
       expR st' env e (st'', Rval v) ->
       argR st env (e::es) (st'', Rval (v::vs)).


(*---------------------------TOP LEVEL DECL IS FUTURE WORK-----------------------

  Inductive combineDecResultR (env : sem_env val) : result (sem_env val) val -> result (sem_env val) val -> Prop :=
    | combineRerr : forall (e : error_result val), 
        combineDecResultR env (Rerr e) (Rerr e)
    | combineRval : forall (env' : sem_env val),
        combineDecResultR env (Rval env') (Rval {| sev := nsAppend (sev env') (sev env);
                                                   sec := nsAppend (sec env') (sec env) |}).
                                                   (* TODO: use extend_dec_env *)

  Inductive decR (A : Type) (st : state A) (env : sem_env val) : dec -> (state A) * (result (sem_env val) val) -> Prop :=

    | Dlet_R : forall (st' st'' : state A) (env' : sem_env val) (sto : store val) (l : locs)
                 (p : pat) (e : exp) (v : val) (res : result (sem_env val) val),
        expR st env e (st', Rval v) -> 
        sto = refs st' -> 
        pmatchR sto env p v (Match env') ->
        decR st env (Dlet l p e) (st'', res)

    | DletExpFail_R : forall (st' st'' : state A) (env' : sem_env val) (sto : store val) (l : locs)
                        (p : pat) (e : exp) (err_v : error_result val) (res : result (sem_env val) val),
        expR st env e (st', Rerr err_v) -> 
        decR st env (Dlet l p e) (st', Rerr err_v)

    | DletMatFail_R : forall (st' st'' : state A) (env' : sem_env val) (sto : store val) (l : locs)
                        (p : pat) (e : exp) (v : val) (res : result (sem_env val) val),
        expR st env e (st', Rval v) -> 
        sto = refs st' -> 
        pmatchR sto env p v No_match ->
        decR st env (Dlet l p e) (st', res)

    (* Stuff hidden by build_rec_env *)
    | Dletrec_R : forall (sev' : env_val) (l : locs) (funs : list (varN * varN * exp)),
        sev' = build_rec_env funs env (sev env)->
        decR st env (Dletrec l funs) (st, Rval {| sev := sev' ; sec := sec env |})

    | Dtype_R : forall (env' : sem_env val) (st' st'' : state A) (res : result (sem_env val) val)
                  (l : locs) (t : typeDef) (tds : typeDef) ,
        st' = {| clock := clock st;
                 refs := refs st;
                 ffi := ffi st;
                 next_type_stamp := next_type_stamp st + length tds;
                 next_exn_stamp := next_exn_stamp st|} ->
        env' = {| sev := nsEmpty ; sec := build_tdefs (next_type_stamp st) tds |} ->
        decR st env (Dtype l t) (st', res)

    | Dtabbrev_R : forall (loc : locs) (res : result (sem_env val) val)
                     (tvs : list tvarN) (tn : typeN) (t : ast_t),
        res = Rval {| sev := nsEmpty; sec := nsEmpty |} ->
        decR st env (Dtabbrev loc tvs tn t) (st, res)

    | Dexn_R : forall (st' : state A) (res : result (sem_env val) val)
                 (loc : locs) (cn : conN) (ts : list ast_t),
        st' = {| clock := clock st;
                 refs := refs st;
                 ffi := ffi st;
                 next_type_stamp := next_type_stamp st;
                 next_exn_stamp := next_exn_stamp st + 1|} ->
        decR st env (Dexn loc cn ts)
             (st', Rval {| sev := nsEmpty; sec := nsSing cn (length ts, ExnStamp (next_exn_stamp st)) |})

    | Dmod_R_Succ : forall (st' st'' : state A) (env' : sem_env val) (res : result (sem_env val) val)
                      (mn : modN) (ds : list dec) (d : dec),
        decListR st env ds (st', Rval env') ->
        decR st' {| sev := nsLift mn (sev env'); sec := nsLift mn (sec env') |} d (st'', res) ->
        decR st env (Dmod mn ds) (st'', res)

    | Dmod_R_Fail : forall (st' : state A) (mn : modN) (ds : list dec) (d : list dec) (err_v : error_result val),
        decListR st env ds (st', Rerr err_v) ->
        decR st env (Dmod mn ds) (st', Rerr err_v)

    | Dlocal : forall (st' st'' st''' : state A) (env' : sem_env val) (lds ds : list dec)
                 (d : list dec) (res : result (sem_env val) val),
        decListR st env lds (st', Rval env') ->
        decListR st' env' ds (st'', res) ->
        decR st env (Dlocal lds ds) (st'', res)

  with decListR (A : Type) (st : state A) (env : sem_env val) : list dec -> (state A) * (result (sem_env val) val) -> Prop :=
    | Dnil_R : 
        decListR st env [] (st, Rval {| sev := nsEmpty; sec := nsEmpty |})
    | DconsRval_R : forall (st' st'' : state A) (env' env'': sem_env val) (d : dec) (ds : list dec) (res res': result (sem_env val) val),
        decR st env d (st', res) -> 
        combineDecResultR env res (Rval env') ->
        decListR st' env' ds (st'', res) -> decListR st env (d::ds) (st'', Rval env'')

*)




(*--------------------------------------------------------------
LATER: treatment of exceptions and the propagation of exceptions 

  | ERaise_R  : forall (st': state A) (e : exp) (v :val),
      expR st env e (st', Rval v) -> 
      expR st env (ERaise e) (st', Rerr (Rraise v))

  | EHandleCatch_R : forall (st' st'': state A) (e : exp) (l : list (pat * exp)) (err_v : val) (r : result val val),
      expR st env e (st', Rerr (Rraise err_v)) ->
      matR st' env err_v l err_v (st'', r) ->
      expR st env (EHandle e l) (st'', r)

   | ArgsFail : forall (st' st'': state A) (res_val : result (list val) val) (err : error_result val) (e : exp) (es : list exp),
       argR st env es (st', res_val) -> expR st' env e (st'', Rerr err) ->
       argR st env (e::es) (st'', Rerr err)
   | ArgsPrevFail : forall (st' st'' : state A) (e : exp) (v : val) (es : list exp) (err : error_result val),
       argR st env es (st', Rerr err) -> argR st env (e::es) (st', Rerr err)
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
*)





(** QUESTION: would it make sense that the recursive closures store as environment not [env]
    but directly [env with v = build_rec_env funs env env.v], rather than rebuilding 
    this extended environment each time? *)
