Require Import CakeSem.Namespace.
Require Import CakeSem.Utils.
Require Import CakeSem.Word.
Require Import CakeSem.CakeAST.
Require Import CakeSem.SemanticPrimitives.
Require Import String.
Require Import List.
Import  ListNotations.
Require Import ZArith.
Require String.

Open Scope string.

Definition trueConv  := Conv (Some (TypeStamp "True"  bool_type_num)) [].
Definition falseConv := Conv (Some (TypeStamp "False" bool_type_num)) [].

Open Scope Z_scope.

Inductive appR : op -> list val -> val -> Prop :=
| app_OpnPlus : forall (a b : int), appR (Opn Plus) [Litv (IntLit a); Litv (IntLit b)] (Litv (IntLit (a + b)%Z))
| app_OpnMinus : forall (a b : int), appR (Opn Minus) [Litv (IntLit a); Litv (IntLit b)] (Litv (IntLit (a - b)%Z))
| app_OpnTimes : forall (a b : int), appR (Opn Times) [Litv (IntLit a); Litv (IntLit b)] (Litv (IntLit (a * b)%Z))
| app_OpbLtTrue  : forall (a b : int), a < b -> appR (Opb Lt) [Litv (IntLit a); Litv (IntLit b)] trueConv  (* could probably shorten by using boolean comparison *)
| app_OpbLtFalse : forall (a b : int), not (a < b) -> appR (Opb Lt) [Litv (IntLit a); Litv (IntLit b)] falseConv
| app_OpbGtTrue  : forall (a b : int), a > b -> appR (Opb Gt) [Litv (IntLit a); Litv (IntLit b)] trueConv
| app_OpbGtFalse : forall (a b : int), not (a > b) -> appR (Opb Gt) [Litv (IntLit a); Litv (IntLit b)] falseConv
| app_OpbLeqTrue  : forall (a b : int), a <= b -> appR (Opb Leq) [Litv (IntLit a); Litv (IntLit b)] trueConv
| app_OpbLeqFalse : forall (a b : int), not (a <= b) -> appR (Opb Leq) [Litv (IntLit a); Litv (IntLit b)] falseConv
| app_OpbGeqTrue  : forall (a b : int), a >= b -> appR (Opb Geq) [Litv (IntLit a); Litv (IntLit b)] trueConv
| app_OpbGeqFalse : forall (a b : int), not (a >= b) -> appR (Opb Geq) [Litv (IntLit a); Litv (IntLit b)] falseConv
| app_EqualityTrue  : forall (v1 v2 : val), v1 = v2 -> appR Equality [v1; v2] trueConv
| app_EqualityFalse : forall (v1 v2 : val), v1 <> v2 -> appR Equality [v1; v2] falseConv.

Inductive funcAppR : list val -> env_val -> exp -> Prop :=
| app_OpappClosure : forall (clos v : val) (env : sem_env val) (n : varN) (e : exp) (v : val),
    clos = Closure env n e -> funcAppR [clos; v] (nsBind n v (sev env)) e.


Inductive lappR : lop -> val -> exp -> exp_or_val -> Prop :=
| app_AndTrue  : forall e : exp, lappR And trueConv  e (Exp e)
| app_AndFalse : forall e : exp, lappR And falseConv e (Val falseConv)
| app_OrTrue  : forall e : exp, lappR And trueConv  e (Val trueConv)
| app_OrFalse : forall e : exp, lappR And falseConv e (Exp e).

Inductive pmatchR : sem_env val -> pat -> val -> match_result (sem_env val) -> Prop :=
| match_Pany : forall (env: sem_env val) (v : val), pmatchR env Pany v (Match env)

| match_Pvar : forall (env env' : sem_env val) (v : val) (x : varN),
    env' = {| sev := nsBind x v (sev env); sec := sec env|} -> pmatchR env (Pvar x) v (Match env')

| match_Plit : forall (env : sem_env val) (v : val) (l : lit),
    pmatchR env (Plit l) (Litv l) (Match env)

| nomatch_Plit : forall (env : sem_env val) (v : val) (l l' : lit),
    l <> l' -> pmatchR env (Plit l) (Litv l) No_match

| match_Pcon : forall (env env': sem_env val) (n : ident modN conN) (c : conN) (l : nat) (s s' : stamp)
                 (ps : list pat) (vs : list val),
    (* 1. constructor stamp is in env *)
    nsLookup n (sec env) = Some (l,s) ->
    (* 2. stamps have the same type and number of args matches number of patterns *)
    s = s' -> l = length ps ->
    (* 3. every arguement matches its corresponding pattern *)
    pmatchlistR env ps vs (Match env') -> pmatchR env (Pcon (Some n) ps) (Conv (Some s') vs) (Match env')

| nomatch_Pcon : forall (env env': sem_env val) (n : ident modN conN) (on : option (ident modN conN))
                   (c : conN) (l : nat) (s s' : stamp) (os : option stamp)
                 (ps : list pat) (vs : list val),
    (* 0. one name exists and the other does not *)
    (on = Some n /\ os = None) \/ (on = None /\ os = Some s') \/
    (* 1. constructor stamp is not in env *)
    (on = Some n /\ nsLookup n (sec env) = None) \/
    (* 2. stamp is in env but has different type or number of args and match number of patterns unequal *)
    (on = Some n /\ nsLookup n (sec env) = Some (l,s) /\ s <> s') \/ l <> length ps \/
    (* 3. not every argument matches its corresponding pattern *)
    pmatchlistR env ps vs No_match -> pmatchR env (Pcon on ps) (Conv os vs) No_match

(* matching lengths of pattern arguments and constructor arguments enforced by pmatchlistR *)
with pmatchlistR : (sem_env val) -> list pat -> list val -> match_result (sem_env val) -> Prop :=
| pmatch_empty : forall (env : sem_env val), pmatchlistR env [] [] (Match env)
| pmatch_cons_succ : forall (env env' env'' : sem_env val) (p : pat) (ps : list pat) (v : val) (vs : list val),
    pmatchR env p v (Match env') -> pmatchlistR env' ps vs (Match env'') -> pmatchlistR env (p::ps) (v::vs) (Match env'')

| pmatch_cons_fail : forall (env env' : sem_env val) (p : pat) (ps : list pat)
                       (v : val) (vs : list val) (res : match_result (sem_env val)),
    pmatchR env p v No_match -> pmatchlistR env' ps vs res -> pmatchlistR env (p::ps) (v::vs) No_match.

Inductive expR : sem_env val -> exp -> result val val -> Prop :=
| ERaise_R  : forall (env : sem_env val) (e : exp) (v :val),
    expR env e (Rval v) -> expR env (ERaise e) (Rerr (Rraise v))

| EHandleSucc_R : forall (env : sem_env val) (e : exp) (l : list (pat * exp)) (v : val),
    expR env e (Rval v) -> expR env (EHandle e l) (Rval v)

| EHandleCatchEmpty_R : forall (env : sem_env val) (e : exp) (l : list (pat * exp)) (err_v : val),
    expR env e (Rerr (Rraise err_v)) -> l = [] -> expR env (EHandle e l) (Rerr (Rraise err_v))

| EHandleCatchConsMatchSucc_R : forall (env env' : sem_env val) (p : pat) (e e' e'' : exp)
                                  (pes pes' : list (pat * exp)) (err_v : val) (v : result val val),
    expR env e (Rerr (Rraise err_v)) -> pes = (p,e')::pes' -> pmatchR env p err_v (Match env') ->
    expR env' e' v -> expR env (EHandle e'' pes) v

| EHandleCatchConsMatchFail_R : forall (env : sem_env val) (p : pat) (e e' e'' : exp)
                                  (pes : list (pat * exp)) (err_v v : val),
    expR env e (Rerr (Rraise err_v)) ->
    Forall (fun pe : (pat * exp) => match pe with
                                   (pt,ex) => pmatchR env p err_v No_match
                                 end) pes ->
    expR env (EHandle e'' pes) (Rval v)

| ELit_R    : forall (l : lit) (env : sem_env val), expR env (ELit l) (Rval (Litv l))

| EConNamed_R   : forall (env : sem_env val) (es : list exp) (vs : list val)
                  (o : option (ident modN conN)) (i : ident modN conN) (n : nat) (s : stamp),
    o = Some i -> nsLookup i (sec env) = Some (n, s) -> n = length es /\ n = length vs ->
    argR env es vs -> expR env (ECon o es) (Rval (Conv (Some s) vs))

(* ??Anonymous Constructor?? *)
| EConUnnamed_R : forall (env : sem_env val) (es : list exp) (vs : list val) (i : ident modN conN) (n : nat),
    n = length (es) /\ n = length (vs) -> argR env es vs -> expR env (ECon None es) (Rval (Conv None vs))

| EVar_R : forall (v : val) (i : ident modN varN) (env : sem_env val),
    Some v = nsLookup i (sev env) -> expR env (EVar i) (Rval v)

| EFun_R : forall (env env' : sem_env val) (sev' : env_val) (e : exp) (v : val) (vname : varN),
    expR env e (Rval v) -> sev' = nsBind vname v (sev env) -> env' = {| sev := sev'; sec := (sec env) |} ->
    expR env (EFun vname e) (Rval (Closure env' vname e))

| EAppPrimitive_R : forall (env : sem_env val) (o : op) (es : list exp) (v : val) (vs : list val),
    argR env es vs -> appR o vs v -> expR env (EApp o es) (Rval v)
| EAppFunction_R  : forall (env : sem_env val) (env' : env_val) (e : exp) (es : list exp) (v : val) (vs : list val),
    argR env es vs -> funcAppR vs env' e -> expR {|sev := env'; sec := sec env|} e (Rval v) -> expR env (EApp Opapp es) (Rval v)

| ELogVal_R : forall (env : sem_env val) (op : lop) (e1 e2 : exp) (v v1: val),
    expR env e1 (Rval v1) -> lappR op v1 e2 (Val v) -> expR env (ELog op e1 e2) (Rval v)
| ELogExp_R : forall (env : sem_env val) (op : lop) (e e1 e2 : exp) (v v1: val),
    expR env e1 (Rval v1) -> lappR op v1 e2 (Exp e) -> expR env e (Rval v) -> expR env (ELog op e1 e2) (Rval v)

| EIfTrue_R  : forall (env : sem_env val) (c t e : exp) (v : val),
    expR env c (Rval trueConv)  -> expR env t (Rval v) -> expR env (EIf c t e) (Rval v)
| EIfFalse_R : forall (env : sem_env val) (c t e : exp) (v : val),
    expR env c (Rval falseConv) -> expR env e (Rval v) -> expR env (EIf c t e) (Rval v)

| ELet_R : forall (env env' : sem_env val) (sev' : env_val) (e1 e2 : exp) (v1 v2 : val) (o : option varN ),
    expR env e1 (Rval v1) -> sev' = nsOptBind o v1 (sev env) -> env' = {| sev := sev'; sec := sec env|} ->
    expR env' e2 (Rval v2) -> expR env (ELet o e1 e2) (Rval v2)

| ELetrec_R : forall (env env': sem_env val) (sev' : env_val) (e : exp) (v : val) (lns : list (varN * varN * exp)),
    sev' = build_rec_env lns env (sev env) -> env' = {| sev := sev'; sec := sec env |} ->
    expR env' e (Rval v) -> expR env (ELetrec lns e) (Rval v)

with argR : sem_env val -> list exp -> list val -> Prop :=
     | NoArgs : forall (env : sem_env val), argR env [] []
     | Args : forall (env : sem_env val) (e : exp) (v : val) (es : list exp) (vs : list val),
         expR env e (Rval v) -> argR env (e::es) (v::vs)

(* Maybe separate out matR, not necessarily dependent on expR. *)
(* Just return the expression or the error value?  *)
with matR : sem_env val -> val -> list (pat * exp) -> val -> result val val -> Prop :=
     | matNil  : forall (env : sem_env val) (v err_v : val),
         matR env v [] err_v (Rerr (Rraise err_v))
     | matConsMatch : forall (env env' : sem_env val) (v err_v : val) (p : pat) (e :exp)
                   (pes pes' : list (pat * exp)) (ret : result val val),
         pmatchR env p v (Match env') -> expR env' e ret -> matR env v ((p,e)::pes') err_v ret
     | matConsNoMatch : forall (env env' : sem_env val) (v err_v : val) (p : pat) (e :exp)
                   (pes pes' : list (pat * exp)) (ret : result val val),
         pmatchR env p v No_match -> matR env v pes' err_v ret -> matR env v ((p,e)::pes') err_v ret.