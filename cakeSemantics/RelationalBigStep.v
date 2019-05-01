Require Import CakeSem.Namespace.
Require Import CakeSem.Utils.
Require Import CakeSem.Word.
Require Import CakeSem.CakeAST.
Require Import CakeSem.SemanticPrimitives.
Require Import CakeSem.ffi.FFI.
Require Import String.
Require Import List.
Import  ListNotations.
Require Import ZArith.
Require String.

Open Scope string.

Definition trueConv  := Conv (Some (TypeStamp "True"  bool_type_num)) [].
Definition falseConv := Conv (Some (TypeStamp "False" bool_type_num)) [].

Open Scope Z_scope.
(* do_app *)
Inductive appR (A FFI : Type) (s : store A) (t : ffi_state FFI) : op -> list val -> store A -> ffi_state FFI -> val -> Prop :=
| app_OpnPlus : forall (a b : int), appR A FFI s t (Opn Plus) [Litv (IntLit a); Litv (IntLit b)] s t (Litv (IntLit (a + b)%Z))
| app_OpnMinus : forall (a b : int), appR A FFI s t (Opn Minus) [Litv (IntLit a); Litv (IntLit b)] s t (Litv (IntLit (a - b)%Z))
| app_OpnTimes : forall (a b : int), appR A FFI s t (Opn Times) [Litv (IntLit a); Litv (IntLit b)] s t (Litv (IntLit (a * b)%Z))
| app_OpbLtTrue  : forall (a b : int), a < b -> appR A FFI s t (Opb Lt) [Litv (IntLit a); Litv (IntLit b)] s t trueConv  (* could probably shorten by using boolean comparison *)
| app_OpbLtFalse : forall (a b : int), not (a < b) -> appR A FFI s t (Opb Lt) [Litv (IntLit a); Litv (IntLit b)] s t falseConv
| app_OpbGtTrue  : forall (a b : int), a > b -> appR A FFI s t (Opb Gt) [Litv (IntLit a); Litv (IntLit b)] s t trueConv
| app_OpbGtFalse : forall (a b : int), not (a > b) -> appR A FFI s t (Opb Gt) [Litv (IntLit a); Litv (IntLit b)] s t falseConv
| app_OpbLeqTrue  : forall (a b : int), a <= b -> appR A FFI s t (Opb Leq) [Litv (IntLit a); Litv (IntLit b)] s t trueConv
| app_OpbLeqFalse : forall (a b : int), not (a <= b) -> appR A FFI s t (Opb Leq) [Litv (IntLit a); Litv (IntLit b)] s t falseConv
| app_OpbGeqTrue  : forall (a b : int), a >= b -> appR A FFI s t (Opb Geq) [Litv (IntLit a); Litv (IntLit b)] s t trueConv
| app_OpbGeqFalse : forall (a b : int), not (a >= b) -> appR A FFI s t (Opb Geq) [Litv (IntLit a); Litv (IntLit b)] s t falseConv
| app_EqualityTrue  : forall (v1 v2 : val), v1 = v2 -> appR A FFI s t Equality [v1; v2] s t trueConv
| app_EqualityFalse : forall (v1 v2 : val), v1 <> v2 -> appR A FFI s t Equality [v1; v2] s t falseConv.

(* do_opapp *)
(* this is bad. Same thing as usual, too many function applications will probably blow up in proofs *)
Inductive funcAppR : list val -> sem_env val -> exp -> Prop :=
| app_OpappClosure : forall (clos v : val) (env env': sem_env val) (n : varN) (e : exp) (v : val),
    clos = Closure env n e -> env' = {| sev := (nsBind n v (sev env)); sec := sec env|} -> funcAppR [clos; v] env'  e
| app_OpappRecclosure : forall (clos v : val) (env env': sem_env val) (ev' : env_val) (l : list (varN * varN * exp)) (n : varN) (e : exp) (v : val),
    clos = Recclosure env l n ->
    allDistinct string_dec (List.map (fun trip => match trip with (f,_,_) => f end) l) = true ->
    ev' = build_rec_env l env (sev env) -> env' = {| sev := ev'; sec := sec env |} -> funcAppR [clos; v] env' e.

Inductive lappR : lop -> val -> exp -> exp_or_val -> Prop :=
| app_AndTrue  : forall e : exp, lappR And trueConv  e (Exp e)
| app_AndFalse : forall e : exp, lappR And falseConv e (Val falseConv)
| app_OrTrue  : forall e : exp, lappR And trueConv  e (Val trueConv)
| app_OrFalse : forall e : exp, lappR And falseConv e (Exp e).

Inductive pmatchR : store val -> sem_env val -> pat -> val -> match_result (sem_env val) -> Prop :=
| match_Pany : forall (sto : store val) (env: sem_env val) (v : val), pmatchR sto env Pany v (Match env)

| match_Pvar : forall (sto : store val) (env env' : sem_env val) (v : val) (x : varN),
    env' = {| sev := nsBind x v (sev env); sec := sec env|} -> pmatchR sto env (Pvar x) v (Match env')

| match_Plit : forall (sto : store val) (env : sem_env val) (v : val) (l : lit),
    pmatchR sto env (Plit l) (Litv l) (Match env)

| nomatch_Plit : forall (sto : store val) (env : sem_env val) (v : val) (l l' : lit),
    l <> l' -> pmatchR sto env (Plit l) (Litv l) No_match

| match_Pcon : forall (sto : store val) (env env': sem_env val) (n : ident modN conN) (c : conN) (l : nat) (s s' : stamp)
                 (ps : list pat) (vs : list val),
    (* 1. constructor stamp is in env *)
    nsLookup n (sec env) = Some (l,s) ->
    (* 2. stamps have the same type and number of args matches number of patterns *)
    s = s' -> l = length ps ->
    (* 3. every arguement matches its corresponding pattern *)
    pmatchlistR sto env ps vs (Match env') -> pmatchR sto env (Pcon (Some n) ps) (Conv (Some s') vs) (Match env')

| nomatch_Pcon : forall (sto : store val) (env env': sem_env val) (n : ident modN conN) (on : option (ident modN conN))
                   (c : conN) (l : nat) (s s' : stamp) (os : option stamp)
                 (ps : list pat) (vs : list val),
    (* 0. one name exists and the other does not *)
    (on = Some n /\ os = None) \/ (on = None /\ os = Some s') \/
    (* 1. constructor stamp is not in env *)
    (on = Some n /\ nsLookup n (sec env) = None) \/
    (* 2. stamp is in env but has different type or number of args and match number of patterns unequal *)
    (on = Some n /\ nsLookup n (sec env) = Some (l,s) /\ s <> s') \/ l <> length ps \/
    (* 3. not every argument matches its corresponding pattern *)
    pmatchlistR sto env ps vs No_match -> pmatchR sto env (Pcon on ps) (Conv os vs) No_match

| match_Pref : forall (sto : store val) (env env' : sem_env val) (lnum : nat) (p : pat) (v : val),
   store_lookup lnum sto = Some (Refv v) -> pmatchR sto env p v (Match env') -> pmatchR sto env (Pref p) (Loc lnum) (Match env')

| match_Ptannot : forall (sto : store val) (env : sem_env val) (p : pat) (v : val) (t : ast_t) (m : match_result (sem_env val)),
    pmatchR sto env p v m -> pmatchR sto env (Ptannot p t) v m

(* matching lengths of pattern arguments and constructor arguments enforced by pmatchlistR *)
with pmatchlistR : store val -> sem_env val -> list pat -> list val -> match_result (sem_env val) -> Prop :=
| pmatch_empty : forall (sto : store val) (env : sem_env val), pmatchlistR sto env [] [] (Match env)
| pmatch_cons_succ : forall (sto : store val) (env env' env'' : sem_env val) (p : pat) (ps : list pat) (v : val) (vs : list val),
    pmatchR sto env p v (Match env') -> pmatchlistR sto env' ps vs (Match env'') -> pmatchlistR sto env (p::ps) (v::vs) (Match env'')

| pmatch_cons_fail : forall (sto : store val) (env env' : sem_env val) (p : pat) (ps : list pat)
                       (v : val) (vs : list val) (res : match_result (sem_env val)),
    pmatchR sto env p v No_match -> pmatchlistR sto env' ps vs res -> pmatchlistR sto env (p::ps) (v::vs) No_match.

Inductive expR (A : Type) (st : state A) (env : sem_env val) : exp -> (state A) * result val val -> Prop :=
| ELit_R    : forall (l : lit), expR A st env (ELit l) (st, Rval (Litv l))

| ERaise_R  : forall (st': state A) (e : exp) (v :val),
    expR A st env e (st', Rval v) -> expR A st env (ERaise e) (st', Rerr (Rraise v))

| EHandleCatch_R : forall (st' st'': state A) (e : exp) (l : list (pat * exp)) (err_v : val) (r : result val val),
    expR A st env e (st', Rerr (Rraise err_v)) -> matR A st' env err_v l err_v (st'', r) ->
    expR A st env (EHandle e l) (st'', r)

(* might be too many helper functions here: do_con_check is hiding alot and rev is usually a pain when trying to use abstractly *)
| EConNamed_R : forall (st' : state A) (es : list exp) (vs : list val) (o : option (ident modN conN)) (i : ident modN conN) (n : nat) (s : stamp),
    do_con_check (sec env) o n = true -> argR A st env (rev es) (st', Rval vs) -> expR A st env (ECon o es) (st', Rval (Conv (Some s) vs))

(* ??Anonymous Constructor?? *)
(* only needed if getting rid of do_con_check*)
(* | EConUnnamed_R : forall (st' : state A) (es : list exp) (vs : list val) (i : ident modN conN) (n : nat), *)
(*     n = length (es) /\ n = length (vs) -> argR A st env es (st', Rval vs) -> expR A st env (ECon None es) (st, Rval (Conv None vs)) *)


| EVar_R : forall (v : val) (i : ident modN varN),
    Some v = nsLookup i (sev env) -> expR A st env (EVar i) (st, Rval v)

| EFun_R : forall (e : exp) (v : val) (vname : varN),
    expR A st env (EFun vname e) (st, Rval (Closure env vname e))

(* old one *)
(* | EFun_R : forall (env env' : sem_env val) (sev' : env_val) (e : exp) (v : val) (vname : varN), *)
(*     expR env e (Rval v) -> sev' = nsBind vname v (sev env) -> env' = {| sev := sev'; sec := (sec env) |} -> *)
(*     expR env (EFun vname e) (Rval (Closure env' vname e)) *)

| EAppPrimitive_R : forall (st' st'' : state A) (s s' : store val) (t t' : ffi_state A) (o : op) (es : list exp) (v : val) (vs : list val),
    argR A st env (rev es) (st', Rval vs) -> appR _ A (refs st') (ffi st') o vs s' t' v ->
    st'' = {| clock := clock st';
              refs := s';
              ffi := t';
              next_type_stamp := next_type_stamp st' ;
              next_exn_stamp := next_exn_stamp st' |} ->
    expR A st env (EApp o es) (st'', Rval v)

| EAppFunction_R  : forall (st' st'': state A) (env' : sem_env val)  (e : exp) (es : list exp) (v : val) (vs : list val),
    argR A st env (rev es) (st', Rval vs) -> funcAppR vs env' e ->
    expR A st' {|sev := sev env'; sec := sec env|} e (st'', Rval v) -> expR A st env (EApp Opapp es) (st', Rval v)

| ELogVal_R : forall (env' : sem_env val) (st' : state A) (op : lop) (e1 e2 : exp) (v v1: val),
    expR A st env e1 (st', Rval v1) -> lappR op v1 e2 (Val v) -> expR A st env (ELog op e1 e2) (st', Rval v)
| ELogExp_R : forall (env' : sem_env val) (st' st'' : state A) (op : lop) (e e1 e2 : exp) (v v1: val),
    expR A st env e1 (st', Rval v1) -> lappR op v1 e2 (Exp e) -> expR A st' env e (st'', Rval v) -> expR A st env (ELog op e1 e2) (st'', Rval v)

| EIfTrue_R  : forall (st' st'' : state A) (c t e : exp) (v : result val val),
    expR A st env c (st', Rval trueConv) -> expR A st' env t (st'',v) -> expR A st env (EIf c t e) (st'',v)
| EIfFalse_R : forall (st' st'' : state A) (c t e : exp) (v : result val val),
    expR A st env c (st', Rval falseConv) -> expR A st' env e (st'', v) -> expR A st env (EIf c t e) (st'', v)

| EMatVal_R : forall (st' : state A) (env' : sem_env val) (e : exp) (pes : list (pat * exp)) (v : val) (a : result val val),
    expR A st env e (st', Rval v) -> matR A st env v pes bind_exn_v (st', a) -> expR A st env (EMat e pes) (st, a)

| ELet_R : forall (st' st'' : state A) (env' : sem_env val) (sev' : env_val) (e1 e2 : exp) (v1 v2 : val) (o : option varN ),
    expR A st env e1 (st', Rval v1) -> sev' = nsOptBind o v1 (sev env) -> env' = {| sev := sev'; sec := sec env|} ->
    expR A st' env' e2 (st'', Rval v2) -> expR A st env (ELet o e1 e2) (st'', Rval v2)

(* hiding behind a function again (build_rec_env) *)
| ELetrec_R : forall (st' st'' : state A) (env': sem_env val) (sev' : env_val) (e : exp) (v : val) (funs : list (varN * varN * exp)),
    sev' = build_rec_env funs env (sev env) -> env' = {| sev := sev'; sec := sec env |} ->
    expR A st env' e (st', Rval v) -> expR A st env (ELetrec funs e) (st', Rval v)

| ETannot_R : forall (st' : state A) (e : exp) (t : ast_t) (r : result val val),
    expR A st env e (st', r) -> expR A st env (ETannot e t) (st', r)

| ELannot_R : forall (st' : state A) (e : exp) (l : locs) (r : result val val),
    expR A st env e (st', r) -> expR A st env (ELannot e l) (st', r)

(* This is bad, very very bad. There has to be a way of doing this better *)
(* This works because P \/ Q -> R has the same effect as P -> R & Q -> R *)
| Fallthrough : forall (e e' : exp) (st' : state A) (res : result val val),
    (exists (l : list (pat * exp)), e' = EHandle e l) \/
    (exists (err : error_result val), e' = ERaise e /\ res = Rerr err)
    (* (exists (i : id )ent modN varN), None = nsLookup i (sev env) /\ e' = EVar i) \/ *)
    (* (exists (o : op) (es : list exp), e' = EApp op es /\ res = Rerr err) \/ *)
    (* (exists (op : lop) (v : val) (e1 e2 : exp), e' = ELog op e1 e2) \/ *)
    (* (exists (e : exp) (pes : list (pat * exp)), e' = EMat e pes /\ res = Rerr v) \/ *)
    ->
    expR A st env e (st', res) -> expR A st env e' (st', res)

with argR (A :Type) (st : state A) (env : sem_env val) : list exp -> ((state A) * result (list val) val) -> Prop :=
     | NoArgs : argR A st env [] (st, Rval [])
     | ArgsSucc : forall (st' st'' : state A) (e : exp) (v : val) (es : list exp) (vs : list val),
         expR A st env e (st', Rval v) -> argR A st' env es (st'', Rval vs) -> argR A st env (e::es) (st', Rval (v::vs))
     (* GTF = Going To Fail *)
     | ArgsGTF : forall (st' st'' : state A) (e : exp) (v : val) (es : list exp) (err : error_result val),
         expR A st env e (st', Rval v) -> argR A st' env es (st'', Rerr err) -> argR A st env (e::es) (st', Rerr err)
     | ArgsFail : forall (st' st'': state A) (err : error_result val) (e : exp) (es : list exp),
         expR A st env e (st', Rerr err) -> argR A st env (e::es) (st', Rerr err)

(* Maybe separate out matR, not necessarily dependent on expR. *)
(* Just return the expression or the error value?  *)
with matR (A : Type) (st : state A) (env : sem_env val) : val -> list (pat * exp) -> val -> (state A) * result val val -> Prop :=
     | matNil  : forall (v err_v : val), matR A st env v [] err_v (st, Rerr (Rraise err_v))
     | matConsMatch : forall (sto : store val) (env' : sem_env val) (v err_v : val) (p : pat) (e :exp)
                        (pes pes' : list (pat * exp)) (ret : (state A) * result val val),
         sto = refs st -> pmatchR sto env p v (Match env') -> expR A st env' e ret -> matR A st env v ((p,e)::pes') err_v ret
     | matConsNoMatch : forall (sto : store val) (env' : sem_env val) (v err_v : val) (p : pat) (e :exp)
                          (pes pes' : list (pat * exp)) (ret : (state A) * result val val),
         sto = refs st -> pmatchR sto env p v No_match -> matR A st env v pes' err_v ret -> matR A st env v ((p,e)::pes') err_v ret.

Inductive combineDecResultR (env : sem_env val) : result (sem_env val) val -> result (sem_env val) val -> Prop :=
| combineRerr : forall (e : error_result val), combineDecResultR env (Rerr e) (Rerr e)
| combineRval : forall (env' : sem_env val),
    combineDecResultR env (Rval env') (Rval {| sev := nsAppend (sev env') (sev env);
                                               sec := nsAppend (sec env') (sec env) |}).

Inductive decR (A : Type) (st : state A) (env : sem_env val) : list dec -> (state A) * (result (sem_env val) val) -> Prop :=
| Dnil_R : decR A st env [] (st, Rval {| sev := nsEmpty; sec := nsEmpty |})
| DconsRval_R : forall (st' st'' : state A) (env' env'': sem_env val) (d : dec) (ds : list dec) (res res': result (sem_env val) val),
    decR A st env [d] (st', res) -> combineDecResultR env res (Rval env') ->
    decR A st' env' ds (st'', res) -> decR A st env (d::ds) (st'', Rval env'')
| DconsRerr_R : forall (st' : state A) (d : dec) (ds : list dec) (res : result (sem_env val) val) (err_v : error_result val),
    decR A st env [d] (st', res) -> combineDecResultR env res (Rerr err_v) ->
    decR A st env (d::ds) (st', Rerr err_v)

| Dlet_R : forall (st' st'' : state A) (env' : sem_env val) (sto : store val) (d : list dec) (l : locs)
             (p : pat) (e : exp) (v : val) (res : result (sem_env val) val),
    expR A st env e (st', Rval v) -> sto = refs st' -> pmatchR sto env p v (Match env') ->
    decR A st' env' d (st'', res) -> decR A st env ((Dlet l p e)::d) (st'', res)
| DletExpFail_R : forall (st' st'' : state A) (env' : sem_env val) (sto : store val) (d : list dec) (l : locs)
                    (p : pat) (e : exp) (err_v : error_result val) (res : result (sem_env val) val),
    expR A st env e (st', Rerr err_v) -> decR A st env ((Dlet l p e)::d) (st', Rerr err_v)
| DletMatFail_R : forall (st' st'' : state A) (env' : sem_env val) (sto : store val) (d : list dec) (l : locs)
                    (p : pat) (e : exp) (v : val) (res : result (sem_env val) val),
    expR A st env e (st', Rval v) -> sto = refs st' -> pmatchR sto env p v No_match ->
    decR A st env ((Dlet l p e)::d) (st', res)

(* Stuff hidden by build_rec_env *)
(* Need error handling *)
| Dletrec_R : forall (sev' : env_val) (l : locs) (funs : list (varN * varN * exp)) (d : list dec),
    sev' = build_rec_env funs env (sev env)->
    decR A st env ((Dletrec l funs)::d) (st, Rval {| sev := sev' ; sec := sec env |}).

| Dtype_R : forall (st'' : state A) (l : locs) (tds : typeDef) (tds : list dec),
    st' = {| clock := clock st;
             refs := refs st;
             ffi := ffi st;
             next_type_stamp := next_type_stamp st + length tds ;
             next_exn_stamp := next_exn_stamp st|} ->
    env' = {| sev := nsEmpty ; sec := build_tdefs (next_type_stamp st) tds |} ->
    decR A st env' d (st') ->
    decR A st env ((Dtype l t)::d) (st'', env' )
(* | Dtabbrev_R :  *)
(* | Dexn_R :  *)
(* | Dmod_R :  *)
