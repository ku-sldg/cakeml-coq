Require Import CakeSem.Utils.
Require Import CakeSem.ffi.FFI.
Require Import CakeSem.Namespace.
Require Import CakeSem.CakeAST.
Require Import CakeSem.SemanticsAux.
Require Import StructTact.StructTactics.

Require Import Equations.Prop.Equations.

Require Import Ascii.
Require Import List.
Import ListNotations.
Require Import Lia.
Require Import PeanoNat.
Require Import ZArith.
Require Import ZArith.Zdigits.
Require Import Zbool.

(* Require Import Coq.Wellfounded.Lexicographic_Product. *)
(* Require Import Relation_Operators. *)
(* ---------------------------------------------------------------------- *)
(** ** Helper functions *)
(* Definition ident_string_dec := Namespace.ident_eq_dec _ _ string_dec string_dec. *)
Definition ident_string_beq := CakeAST.ident_beq _ _ String.eqb String.eqb.

(* ---------------------------------------------------------------------- *)
(** ** Store assign *)
Definition store_assign {A : Type} (n : nat) (v : store_v A) (st : store A) : option (store A) :=
  match List.nth_error st n with
  | Some v' => if store_v_same_type v' v
              then Some (update n v st)
              else None
  | _ => None
  end.

(* ---------------------------------------------------------------------- *)
(** ** Constructor comparison *)

Definition same_ctor := stamp_beq.
(*   if stamp_eq_dec s1 s2 then true else false. *)

(* ---------------------------------------------------------------------- *)
(** ** Pattern matcher *)

(* A big-step pattern matcher.  If the value matches the pattern, return an
 * environment with the pattern variables bound to the corresponding sub-terms
 * of the value; this environment extends the environment given as an argument.
 * No_match is returned when there is no match, but any constructors
 * encountered in determining the match failure are applied to the correct
 * number of arguments, and constructors in corresponding positions in the
 * pattern and value come from the same type.  Match_type_error is returned
 * when one of these conditions is violated *)

Open Scope bool_scope.
Equations pmatch : env_ctor -> store val -> pat -> val -> alist varN val -> match_result (alist varN val) :=
  pmatch _ _ Pany _ env => Match env;
  pmatch _ _ (Pvar x) v env => Match ((x,v)::env);
  pmatch _ _ (Plit l) (Litv l') env => if lit_beq l l'
                                         then Match env
                                         else if lit_same_type l l'
                                              then No_match
                                              else Match_type_error;
  pmatch envC s (Pcon (Some cid) ps) (Conv (Some stamp) vs) env with nsLookup ident_string_beq cid envC := {
      pmatch envC s (Pcon (Some cid) ps) (Conv (Some stamp) vs) env None => Match_type_error;
      pmatch envC s (Pcon (Some cid) ps) (Conv (Some stamp) vs) env (Some (l, stamp')) =>
        if stamp_same_type stamp stamp' && (length ps =? l)
        then if same_ctor stamp stamp'
             then if length vs =? l
                  then pmatch_list envC s ps vs env
                  else Match_type_error
             else No_match
        else Match_type_error };

  pmatch envC _ (Pcon None ps) (Conv None vs) env => if length ps =? length vs
                                                    then pmatch_list envC s ps vs env
                                                    else Match_type_error;
  pmatch envC s (Pref p) (Loc lnum) env with store_lookup lnum s => {
      pmatch envC s (Pref p) (Loc lnum) env None => Match_type_error;
      pmatch envC s (Pref p) (Loc lnum) env (Some (Refv v)) => pmatch envC s p v env;
      pmatch envC s (Pref p) (Loc lnum) env (Some (W8array _)) => Match_type_error;
      pmatch envC s (Pref p) (Loc lnum) env (Some (Varray _))  => Match_type_error
    };
  pmatch envC _ (Pas p i) v env => pmatch envC s p v ((i,v)::env);
  pmatch envC _ (Ptannot p _) v env => pmatch envC s p v env;
  pmatch _ _ _ _ _ => Match_type_error;

where pmatch_list : env_ctor -> store val -> list pat -> list val -> alist varN val -> match_result (alist varN val) :=
  pmatch_list _ _ [] [] env => Match env;
  pmatch_list envC s (p::ps) (v::vs) env with pmatch envC s p v env => {
      pmatch_list envC s (p::ps) (v::vs) env No_match => No_match;
      pmatch_list envC s (p::ps) (v::vs) env Match_type_error => Match_type_error ;
      pmatch_list envC s (p::ps) (v::vs) env (Match env') => pmatch_list envC s ps vs env';
    };
  pmatch_list _ _ _ _ _ => Match_type_error.

(* ---------------------------------------------------------------------- *)
(** ** Typechecks *)

Definition do_con_check (cenv : env_ctor)
           (n_opt : constr_id)
           (l : nat) : bool :=
  match n_opt with
  | None => true
  | Some n => match nsLookup ident_string_beq n cenv with
             | None => false
             | Some (l',_) => if Nat.eqb l l' then true else false
             end
  end.

(* ---------------------------------------------------------------------- *)
(** ** Equality test *)

Inductive eq_result : Type :=
| Eq_val : bool -> eq_result
| Eq_type_error.
Scheme Equality for eq_result.

Fixpoint do_eq (v1 v2 : val) : eq_result :=
  let fix eq_result_list (vs1 vs2 : list val) :=
        match vs1, vs2 with
        | [], [] => Eq_val true
        | v1'::vs1', v2'::vs2' =>
            match do_eq v1' v2' with
            | Eq_val true => eq_result_list vs1' vs2'
            | Eq_val false => Eq_val false
            | Eq_type_error => Eq_type_error
            end
        | _,_ => Eq_val false
        end
  in
  match v1, v2 with
  | Litv l1, Litv l2 => if lit_same_type l1 l2
                       then Eq_val (lit_beq l1 l2)
                       else Eq_type_error
  | Loc l1, Loc l2 => Eq_val (Nat.eqb l1 l2)
  | Conv cn1 vs1, Conv cn2 vs2 => if andb (option_beq _ stamp_beq cn1 cn2) (Nat.eqb (length vs1) (length vs2))
                                 then eq_result_list vs1 vs2
                                 else if ctor_same_type cn1 cn2
                                      then Eq_val false
                                      else Eq_type_error
  | Vectorv vs1, Vectorv vs2 => if Nat.eqb (length vs1) (length vs2)
                               then eq_result_list vs1 vs2
                               else Eq_val false
  | Closure _ _ _, Closure _ _ _ => Eq_val true
  | Closure _ _ _, Recclosure _ _ _ => Eq_val true
  | Recclosure _ _ _, Closure _ _ _ => Eq_val true
  | Recclosure _ _ _, Recclosure _ _ _ => Eq_val true
  | _, _ => Eq_type_error
  end.

(* ---------------------------------------------------------------------- *)
(** ** Function call *)

Definition do_opapp (vs : list val) : option (sem_env val * exp) :=
  match vs with
  | (Closure env nfun e)::v::[] =>
    Some (update_sev env (nsBind nfun v (sev env)), e)
  | (Recclosure env funs nfun)::v::[] =>
    if nodup_str (List.map (fun p => match p with (f,x,e) => f end) funs)
    then match find_recfun nfun funs with
         | Some (n,e) =>
            let sev' := nsBind n v (build_rec_env funs env (sev env)) in
            Some (update_sev env sev', e)
         | None => None
         end
    else None
  | _ => None
  end.

(* ---------------------------------------------------------------------- *)
(** ** Primitive function call *)

Definition store_ffi (ffi' : Type) (V : Type) := (store V * ffi_state ffi')%type.

Definition natFromInteger (size : nat) :=
  let fix helper (n' : nat ) (z : Z) : nat :=
      match n' with
      | O => O
      | S n'' =>
        (2 ^ n' * (Z.to_nat (Zdigits.bit_value
                               (Z.testbit (Z.of_nat n'') z)))
             + (helper n'' z))
      end
  in helper size.


Definition word8FromInteger (i : Z) : word 8 := nat_to_word 8 (natFromInteger 8 i)%nat .
Definition word64FromInteger (i : Z) : word 64 :=  nat_to_word 64 (natFromInteger 64%nat i).

(* Missing floating point and real number operations *)
Definition do_app (ffi' : Type) (st : store_ffi ffi' val) (o : op) (vs : list val)
  : option (store_ffi ffi' val * result val val) :=
  let '(s,t) := st in
  match o, vs with
  | ListAppend, [x1;x2] =>
      match val_to_list x1, val_to_list x2 with
      | Some xs, Some ys =>
          Some (st, Rval (list_to_val (xs ++ ys)))
      | _, _ => None
      end
  | Opn o', [Litv (IntLit n1); Litv (IntLit n2)] =>
      if  (Z.eqb n2 0) && ((opn_beq o' Divide) || (opn_beq o' Modulo))
      then Some (st, Rerr (Rraise div_exn_v))
      else Some (st, Rval (Litv (IntLit (opn_lookup o' n1 n2))))
  | Opb o', [Litv (IntLit n1); Litv (IntLit n2)] =>
      Some (st, Rval (Boolv (opb_lookup o' n1 n2)))
  | Opw W8 o', [Litv (Word8Lit w1); Litv (Word8Lit w2)] =>
      Some (st, Rval (Litv (Word8Lit (opw8_lookup o' w1 w2))))
  | Opw W64 o', [Litv (Word64Lit w1); Litv (Word64Lit w2)] =>
      Some (st, Rval (Litv (Word64Lit (opw64_lookup o' w1 w2))))
  (* | FP_bop bop, [Litv (Word64Lit w1); Litv (Word64Lit w2)] => *)
  (*     Some ((s,t),Rval (Litv (Word64Lit (fp_bop bop w1 w2)))) *)
  (* | FP_uop uop, [Litv (Word64Lit w)] => *)
  (*   Some ((s,t),Rval (Litv (Word64Lit (fp_uop uop w)))) *)
  (* | FP_cmp cmp, [Litv (Word64Lit w1); Litv (Word64Lit w2)] => *)
  (*   Some ((s,t),Rval (Boolv (fp_cmp cmp w1 w2))) *)
  | Shift W8 o' n, [Litv (Word8Lit w)] =>
      Some (st, Rval (Litv (Word8Lit (shift8_lookup o' w n))))
  | Shift W64 o' n, [Litv (Word64Lit w)] =>
      Some (st, Rval (Litv (Word64Lit (shift64_lookup o' w n))))
  | Equality, [v1; v2] =>
      match do_eq v1 v2 with
      | Eq_type_error => None
      | Eq_val b => Some (st, Rval (Boolv b))
      end
  | Opassign, [Loc lnum; v] =>
      match store_assign lnum (Refv v) s with
      | Some s' => Some ((s',t), Rval (Conv None []))
      | None => None
      end
  | Opref, [v] =>
      let (s',n) := store_alloc (Refv v) s in
      Some ((s',t), Rval (Loc n))
  | Opderef, [Loc n] =>
      match store_lookup n s with
      | Some (Refv v) => Some (st, Rval v)
      | _ => None
      end
  | Aw8alloc, [Litv (IntLit n); Litv (Word8Lit w)] =>
      if (n <? 0)%Z then
        Some (st, Rerr (Rraise sub_exn_v))
      else
        let (s',lnum) := store_alloc (W8array (List.repeat w (Z.to_nat n))) s
        in Some ((s',t), Rval (Loc lnum))
  | Aw8sub, [Loc lnum; Litv (IntLit i)] =>
      match store_lookup lnum s with
      | Some (W8array ws) =>
          if (i <? 0)%Z
          then Some (st, Rerr (Rraise sub_exn_v))
          else
            let n := Z.to_nat i in
            match List.nth_error ws n with
            | None => Some (st, Rerr (Rraise sub_exn_v))
            | Some n' => Some (st, Rval (Litv (Word8Lit n')))
            end
      | _ => None
      end
  | Aw8sub_unsafe, [Loc lnum; Litv (IntLit i)] =>
      match store_lookup lnum s with
      | Some (W8array ws) =>
          if (i <? 0)%Z
          then None
          else let n := Z.abs_nat i in
               if ((length ws) <=? n)
               then None
               else Some (st, Rval (Litv (Word8Lit (nat_to_word 8 n))))
      | _ => None
      end
  | Aw8length, [Loc n] =>
      match store_lookup n s with
      | Some (W8array ws) => Some (st, Rval (Litv (IntLit (Zlength ws))))
      | _ => None
      end
  | Aw8update, [Loc lnum; Litv (IntLit i); Litv (Word8Lit w)] =>
      match store_lookup lnum s with
      | Some (W8array ws) =>
          if (i <? 0)%Z
          then Some (st, Rerr (Rraise sub_exn_v))
          else let n := Z.abs_nat i in
               if (length ws) <=? n
               then Some (st, Rerr (Rraise sub_exn_v))
               else match store_assign lnum (W8array (update n w ws)) s with
                    | None => None
                    | Some s' => Some ((s',t), Rval (Conv None []))
                    end
      | _ => None
      end
  | Aw8update_unsafe, [Loc lnum; Litv (IntLit i); Litv (Word8Lit w)] =>
      match store_lookup lnum s with
      | Some (W8array ws) =>
          if (i <? 0)%Z
          then None
          else let n := Z.abs_nat i in
               if (length ws) <=? n
               then None
               else match store_assign lnum (W8array (update n w ws)) s with
                    | None => None
                    | Some s' => Some ((s',t), Rval (Conv None []))
                    end
      | _ => None
      end
  | WordFromInt W8, [Litv (IntLit i)] =>
      Some (st, Rval (Litv (Word8Lit (word8FromInteger i))))
  | WordFromInt W64, [Litv (IntLit i)] =>
      Some (st, Rval (Litv (Word64Lit (word64FromInteger i))))
  | WordToInt W8, [Litv (Word8Lit w)] =>
      Some (st, Rval (Litv (IntLit (Z.of_nat (word_to_nat _ w)))))
  | WordToInt W64, [Litv (Word64Lit w)] =>
      Some (st, Rval (Litv (IntLit (Z.of_nat (word_to_nat _ w)))))
  | CopyStrStr, [Litv (StrLit str); Litv (IntLit off); Litv (IntLit len)] =>
      Some (st,
          match copy_array (string_to_list_char str,off) len None with
          | None => Rerr (Rraise sub_exn_v)
          | Some cs => Rval (Litv (StrLit (list_char_to_string cs)))
          end)
  | CopyStrAw8, [Litv (StrLit str); Litv (IntLit off); Litv (IntLit len);
                 Loc dst; Litv (IntLit dstoff)] =>
      match store_lookup dst s with
      | Some (W8array ws) =>
          match copy_array (string_to_list_char str, off) len
                  (Some (map word8_to_char ws, dstoff)) with
          | None => Some (st, Rerr (Rraise sub_exn_v))
          | Some cs =>
              match store_assign dst (W8array (map char_to_word8 cs)) s with
              | Some s' =>  Some ((s',t), Rval (Conv None []))
              | _ => None
              end
          end
      | _ => None
      end
  | CopyAw8Str, [Loc src; Litv (IntLit off); Litv (IntLit len)] =>
      match store_lookup src s with
      | Some (W8array ws) =>
          Some ((s,t),
              match copy_array (ws,off) len None with
              | None => Rerr (Rraise sub_exn_v)
              | Some ws => Rval (Litv (StrLit( list_char_to_string
                                                (map word8_to_char ws))))
              end)
      | _ => None
      end
  | CopyAw8Aw8, [Loc src; Litv (IntLit off); Litv (IntLit len);
                 Loc dst; Litv (IntLit dstoff)] =>
      match store_lookup src s, store_lookup dst s with
      | Some (W8array ws), Some (W8array ds) =>
          match copy_array (ws,off) len (Some (ds,dstoff)) with
          | None => Some ((s,t), Rerr (Rraise sub_exn_v))
          | Some ws =>
              match store_assign dst (W8array ws) s with
              | Some s' => Some ((s',t), Rval (Conv None []))
              | _ => None
              end
          end
      | _, _ => None
      end
  | Ord, [Litv (CharLit c)] =>
      Some (st, Rval (Litv (IntLit (Z.of_nat (nat_of_ascii c)))))
  | Chr, [Litv (IntLit i)] =>
      Some (st, if andb (i <? 0)%Z (255 <? i)%Z
                then Rerr (Rraise chr_exn_v)
                else Rval (Litv (CharLit (ascii_of_nat (Z.to_nat i)))))
  | Chopb op, [Litv (CharLit c1); Litv (CharLit c2)] =>
      Some (st, Rval (Boolv (opb_lookup op (Z.of_nat (nat_of_ascii c1))
                               (Z.of_nat (nat_of_ascii c2)))))
  | Implode, [v] =>
      match val_to_char_list v with
      | Some ls => Some (st, Rval (Litv (StrLit (list_char_to_string ls))))
      | None => None
      end
  | Explode, [v] =>
      match v with
      | Litv (StrLit str) =>
          Some (st, Rval (list_to_val (map (fun c => Litv (CharLit c)) (string_to_list_char str))))
      | _ => None
      end
  | Strsub, [Litv (StrLit str); Litv (IntLit i)] =>
      if (i <? 0)%Z then
        Some (st, Rerr (Rraise sub_exn_v))
      else
        let n := Z.abs_nat i in
        match String.get n str with
        | Some n' => Some (st, Rval (Litv (CharLit n')))
        | None    => Some (st, Rerr (Rraise sub_exn_v))
        end
  | Strlen, [Litv (StrLit str)] =>
      Some (st, Rval (Litv (IntLit (Z.of_nat (String.length str)))))
  | Strcat, [v] =>
      match val_to_list v with
      | Some vs =>
          match vals_to_string vs with
          | Some str =>
              Some (st, Rval (Litv(StrLit str)))
          | _ => None
          end
      | _ => None
      end
  | VfromList, [v] =>
      match val_to_list v with
      | Some vs => Some (st, Rval (Vectorv vs))
      | None    => None
      end
  | Vsub, [Vectorv vs; Litv (IntLit i)] =>
      if (i <? 0)%Z
      then Some (st, Rerr (Rraise sub_exn_v))
      else
        let n := Z.abs_nat i in
        match nth_error vs n with
        | None    => Some (st, Rerr (Rraise sub_exn_v))
        | Some v' => Some (st, Rval v')
        end
  | Vlength, [Vectorv vs] =>
      Some ((s,t), Rval (Litv (IntLit (Z.of_nat (List.length  vs)))))
  | Aalloc, [Litv (IntLit n); v] =>
      if (n <? 0)%Z
      then Some (st, Rerr (Rraise sub_exn_v))
      else
        let (s',lnum) := store_alloc (Varray (List.repeat v (Z.to_nat n))) s
        in Some ((s',t), Rval (Loc lnum))
  | AallocEmpty, [Conv None []] =>
      let (s',lnum) := store_alloc (Varray []) s
      in Some ((s',t), Rval (Loc lnum))
  (* | AallocFixed, vs => *)
  (*     let '(s', lnum) := store_alloc (Varray []) s *)
  (*     in Some ((s',t), Rval (Loc lnum)) *)
  | Asub, [Loc lnum; Litv (IntLit i)] =>
      match store_lookup lnum s with
      | Some (Varray vs) =>
          if (i <? 0)%Z
          then Some ((s,t), Rerr (Rraise sub_exn_v))
          else
            let n := Z.to_nat i in
            match nth_error vs n with
            | None    => Some (st, Rerr (Rraise sub_exn_v))
            | Some v' => Some (st, Rval v')
            end
      | _ => None
      end
  | Asub_unsafe, [Loc lnum; Litv (IntLit i)] =>
      match store_lookup lnum s with
      | Some (Varray vs) =>
          if (i <? 0)%Z
          then None
          else
            let n := Z.abs_nat i in
            match nth_error vs n with
            | None    => None
            | Some v' => Some ((s,t), Rval v')
            end
      | _ => None
      end
  | Alength, [Loc n] =>
      match store_lookup n s with
      | Some (Varray ws) =>
          Some (st, Rval (Litv (IntLit (Zlength ws))))
      | _ => None
      end
  | Aupdate, [Loc lnum; Litv (IntLit i); v] =>
      match store_lookup lnum s with
      | Some (Varray vs') =>
          if (i =? 0)%Z then (* LATER: use a wrapper function for this kind of test *)
            Some ((s,t), Rerr (Rraise sub_exn_v))
          else
            let n := Z.abs_nat i in
            if (length vs') <? n
            then Some (st, Rerr (Rraise sub_exn_v))
            else
              match store_assign lnum (Varray (update n v vs')) s with
              | None => None
              | Some s' => Some ((s',t), Rval (Conv None []))
              end
      | _ => None
      end
  | Aupdate_unsafe, [Loc lnum; Litv (IntLit i); v] =>
      match store_lookup lnum s with
      | Some (Varray vs') =>
          if (i =? 0)%Z then (* LATER: use a wrapper function for this kind of test *) (* QUESTION: Why ? *)
            None
          else
            let n := Z.abs_nat i in
            if (length vs') <? n
            then None
            else
              match store_assign lnum (Varray (update n v vs')) s with
              | None => None
              | Some s' => Some ((s',t), Rval (Conv None []))
              end
      | _ => None
      end
  | ConfigGC, [Litv (IntLit i); Litv (IntLit j)] =>
      Some (st, Rval (Conv None []))
  | FFI n, [Litv(StrLit conf); Loc lnum] =>
      match store_lookup lnum s with
      | Some (W8array ws) =>
          match call_FFI t n (List.map (fun c' => nat_to_word 8 (nat_of_ascii c'))
                                (string_to_list_char conf)) ws with
          | Ffi_return _ t' ws' =>
              match store_assign lnum (W8array ws') s with
              | Some s' => Some ((s', t'), Rval (Conv None []))
              | None => None
              end
          | Ffi_final _ outcome =>
              Some (st, Rerr (Rabort (Rffi_error outcome)))
          end
      | _ => None
      end
  | _,_ => None
  end.

Inductive exp_or_val : Type :=
  | Exp : exp -> exp_or_val
  | Val : val -> exp_or_val.

Definition do_log (op : lop) (v : val) (e : exp) : option exp_or_val :=
  match op with
  | And => if val_beq (Boolv true) v
          then Some (Exp e)
          else if val_beq (Boolv false) v
               then Some (Val v)
               else None

  | Or => if val_beq (Boolv true) v
          then Some (Val v)
          else if val_beq (Boolv false) v
               then Some (Exp e)
               else None
  end.

Definition do_if (v : val) (e1 e2 : exp) : option exp :=
  if val_beq (Boolv true) v
    then Some e1
    else if val_beq (Boolv false) v
         then Some e2
         else None.

(* ---------------------------------------------------------------------- *)

Definition list_result {A B : Type} (res : result A B) : result (list A) B :=
  match res with
  | Rval v => Rval [v]
  | Rerr e => Rerr e
  end.

(* An attempt to use lexicographical induction as the termination condition *)

Equations size_exp (e : exp) : nat :=
| ELit _ => 1;
| EVar _ => 1;
| EHandle e' pes => 1 + size_exp e' + size_pes pes;
| EMat e' pes => 1 + size_exp e' + size_pes pes;
| ELetrec vve e' => 1 + size_exp e' + size_vve vve;
| EFun _ e' => 1 + size_exp e';
| ERaise e' => 1 + size_exp e';
| ETannot e' _ => 1 + size_exp e';
| ELannot e' _ => 1 + size_exp e';
| ECon _ es => 1 + size_exps es;
| EApp _ es => 1 + size_exps es;
| ELet _ e' e'' => 1 + size_exp e' + size_exp e'';
| ELog _ e' e'' => 1 + size_exp e' + size_exp e'';
| EIf  e' e'' e''' => 1 + size_exp e' + size_exp e'' + size_exp e''';
where size_exps (es : list exp) : nat :=
| [] => 0;
| e'::es' => size_exp e' + size_exps es';
where size_pes (pes : list (pat * exp)) : nat :=
  | [] => 0;
  | (_,e)::pes' => 1 + size_exp e + size_pes pes';
where size_vve (vve : list (varN * varN * exp)) : nat :=
| [] => 0;
| (_,_,e)::vve' => 1 + size_exp e + size_vve vve'.

Theorem size_exps_app : forall (es es' : list exp), size_exps (es ++ es') = size_exps es + size_exps es'.
Proof.
  induction es.
  - reflexivity.
  - intro es'.
    simpl. rewrite IHes.
    lia.
Qed.

Theorem size_exps_rev : forall (es : list exp), size_exps (rev es) = size_exps es.
Proof.
  induction es.
  - reflexivity.
  - simpl. rewrite size_exps_app.
    rewrite IHes. simpl. lia.
Qed.

Inductive fuel_size_rel : nat * list exp -> nat * list exp -> Prop :=
| fuel_eq : forall (f : nat) (es es' : list exp), size_exps es < size_exps es' -> fuel_size_rel (f, es) (f, es')
| fuel_less : forall (f f' : nat) (es es' : list exp), f < f' -> fuel_size_rel (f, es) (f', es').

Inductive fuel_size_pes_rel : nat * list (pat * exp) -> nat * list (pat * exp) -> Prop :=
| spfuel_eq : forall (f : nat) (pes pes' : list (pat * exp)), size_pes pes < size_pes pes' -> fuel_size_pes_rel (f, pes) (f, pes')
| spfuel_less : forall (f f' : nat) (pes pes' : list (pat * exp)), f < f' -> fuel_size_pes_rel (f, pes) (f', pes').

Definition Rfuel (f f' : nat) := f < f'.

Definition lex_exps (_ : nat) := list exp.
Definition Rsize (es es' : list exp) := size_exps (es) < size_exps es'.

Theorem Rfuel_wf : well_founded Rfuel.
Proof.
  red. induction a.
  - constructor. intros y H.
    inv H.
  - constructor.
    constructor.
    intros y0 H0.
    inv IHa.
    apply H1.
    unfold Rfuel in *.
    lia.
Qed.

Lemma Rsize_wf' : forall len es, size_exps es <= len -> Acc (Rsize) es.
  intros len.
  induction len; intros; constructor; intros.
  - unfold Rsize in *.
    lia.
  - apply IHlen.
    unfold Rsize in *.
    lia.
Qed.

Theorem Rsize_wf : well_founded Rsize.
Proof.
  red.
  induction a; constructor; intros.
  - inv H.
  - apply Rsize_wf' with (size_exps (a::a0)).
    unfold Rsize in *.
    lia.
Qed.

Definition lex_f_s := lexprod _ _ Rfuel Rsize.
Definition lex_f_s_wf := (wf_lexprod _ _ Rfuel Rsize Rfuel_wf Rsize_wf).

Lemma size_exp_at_least_S : (forall x, 1 <= size_exp x).
Proof.
  Transparent size_exp.
  destruct x; simpl; lia.
  Opaque size_exp.
Defined.

Theorem fuel_size_rel_wf' : forall n m f es, f = n /\ size_exps es <= m \/ f < n  -> Acc fuel_size_rel (f, es).
Proof.
  induction n.
  - induction m.
    + constructor.
      inv H.
      * inv H0.
        intros.
        inv H1.
        lia.
        lia.
      * inv H0.
    + constructor.
      intros.
      inv H.
      inv H1.
      inv H0.
      apply IHm.
      left; split; lia.
      lia.
      lia.
  - induction m.
    + constructor.
      intros; destruct y.
      inv H0.
      * inv H.
        -- inv H0. lia. lia.
        -- apply IHn with (size_exps es). inv H0. lia. lia.
      * inv H.
        -- inv H1.
           apply IHn with (size_exps l).
           lia.
        -- apply IHn with (size_exps l).
           inv H0.
           lia.
           right; lia.
    + constructor.
      intros; destruct y.
      inv H.
      inv H1.
      inv H0.
      apply IHm.
      left; lia.
      apply IHm.
      right; lia.
      inv H0.
      apply IHm.
      right; lia.
      apply IHm.
      right; lia.
Defined.

Theorem fuel_size_rel_wf : well_founded fuel_size_rel.
Proof.
  unfold well_founded.
  destruct a.
  induction n; constructor; intros.
  inv H.
  apply fuel_size_rel_wf' with (n := 0) (m := size_exps l).
  left; lia.
  inv H2.
  inv H.
  apply fuel_size_rel_wf' with (n := S n) (m := size_exps l).
  left; lia.
  apply fuel_size_rel_wf' with f (size_exps es).
  left; lia.
Defined.

(*----------------------------------------------------------------------------*)
(*------------- EQUATIONS VERSION ------------------------------------------- *)
(*----------------------------------------------------------------------------*)


#[local] Instance FSRWellFounded : WellFounded fuel_size_rel.
apply fuel_size_rel_wf.
Qed.

Equations evaluate_match {ffi' : Type} (pes : list (pat * exp)) (fuel : nat) (st : state ffi')
          (env : sem_env val) (matched_v : val) (err_v : val)
          (f : list exp -> nat -> state ffi' -> sem_env val -> state ffi' * result (list val) val)
  : state ffi' * result (list val) val := {
  evaluate_match [] _ st _ _ err_v _ => (st, Rerr (Rraise err_v));
  evaluate_match ((p,e)::pes') fuel st env matched_v err_v f =>
    if nodup_str (pat_bindings p [])
    then (match pmatch (sec env) (refs st) p matched_v [] with
          | Match env_v' =>
            f [e] fuel st
                     {| sev := nsAppend (alist_to_ns env_v') (sev env);
                        sec := (sec env) |}
          | No_match => evaluate_match pes' fuel st env matched_v err_v f
          | Match_type_error => (st, Rerr (Rabort Rtype_error))
          end)
    else (st, Rerr (Rabort Rtype_error)) }.

Definition uu : val := Conv None [].

Inductive lexicographic_rel : nat * nat -> nat * nat -> Prop :=
| fst_eq : forall (n n21 n22 : nat), n21 < n22 -> lexicographic_rel (n, n21) (n, n22)
| fst_less : forall (n11 n12 n21 n22 : nat), n11 < n21 -> lexicographic_rel (n11, n12) (n21, n22).

Theorem lexicographic_rel_wf' : forall n2 m2 n1 m1, n1 = n2 /\ m1 <= m2 \/ n1 < n2  -> Acc lexicographic_rel (n1, m1).
Proof.
  induction n2.
  - induction  m2.
    + constructor.
      intros. destruct y.
      destruct H.
      * destruct H. subst.
        inv H0; lia.
      * lia.
    + constructor. intros. destruct y. destruct H.
      * destruct H.
        apply IHm2.
        inv H0.
        -- left. split; lia.
        -- right; lia.
      * apply IHm2.
        inv H.
  - induction m2; constructor; intros; destruct y; inv H0.
    + apply IHn2 with m1; lia.
    + apply IHn2 with n0; lia.
    + apply IHm2; lia.
    + apply IHm2; lia.
Qed.

#[local] Instance LexRWellFounded : WellFounded lexicographic_rel.
unfold WellFounded. unfold well_founded.
destruct a.
constructor; intros; destruct y.
induction n1.
- inv H.
  + apply lexicographic_rel_wf' with n0 n0.
    right. lia.
  + apply lexicographic_rel_wf' with n n.
    right. lia.
- inv H.
  + apply lexicographic_rel_wf' with (S n1) n0.
    left. lia.
  + apply lexicographic_rel_wf' with n n0.
    right. lia.
Qed.

Equations mutmeasure (b : bool) (arg : if b then list exp else list (pat * exp)) : nat := {
  mutmeasure true es => size_exps es;
  mutmeasure false pes => size_pes pes }.

Scheme Equality for op.
Scheme Equality for list.
Scheme Equality for option.
Scheme Equality for ident.
Scheme Equality for string.
Scheme Equality for prod.

Equations? eval_or_match (sel : bool) (es : if sel then list exp else list (pat * exp))
          (fuel : nat) (st : state nat) (env : sem_env val) (match_v : val) (err_v : val)
  : state nat * result (list val) val by wf (fuel, mutmeasure sel es) lexicographic_rel :=
  eval_or_match true [] _ st _ _ _ => (st, Rval []);
  eval_or_match true (e1::e2::es') fuel st env _ _
    with eval_or_match true [e1] fuel st env uu uu => {
    | (st', Rval vs) with eval_or_match true (e2::es') fuel st' env uu uu => {
      | (st'', Rval vs'') with vs => {
        | [] => (st'', Rval (vs''));
        | v::vs' => (st'', Rval (v::vs''))
        };
      | res => res;
      };
    | res => res
    };
  eval_or_match true [ERaise e'] fuel st env _ _
    with eval_or_match true [e'] fuel st env uu uu => {
    | (st', Rval (v::_)) => (st', Rerr (Rraise v));
    | res => res
    };

  eval_or_match true [EHandle e' l] fuel st env _ _ with
    eval_or_match true [e'] fuel st env uu uu => {
    | (st', Rerr (Rraise v)) => eval_or_match false l fuel st' env v bind_exn_v;
    | res => res
    };

  eval_or_match true [ELit l] _ st _ _ _ => (st, Rval [Litv l]);

  eval_or_match true [EVar n] _ st env _ _
    with nsLookup ident_string_beq n (sev env) => {
    | Some v' => (st, Rval [v']);
    | None => (st, Rerr (Rabort Rtype_error))
    };

  eval_or_match true [ECon cn es'] fuel st env _ _
    with do_con_check (sec env) cn (length es') => {
      | true with eval_or_match true (rev es') fuel st env uu uu => {
        | (st', Rval vs)
          with build_conv (sec env) cn (rev vs) => {
          | Some v' => (st', Rval [v']);
          | None => (st', Rerr (Rabort Rtype_error))
          };
        | res => res
        };
    | false => (st, Rerr (Rabort Rtype_error))
    };

  eval_or_match true [EFun x e] _ st _ _ _ => (st, Rval [Closure env x e]);

  eval_or_match true [EApp op es] 0 st env _ _ => (st, Rerr (Rabort Rtimeout_error));

  eval_or_match true [EApp op es] (S fuel') st env _ _ with
    eval_or_match true (rev es) fuel' st env uu uu => {
    | (st', Rval vs)
      with op_beq op Opapp => {
      | true with do_opapp (rev vs) => {
        | Some (env', e) => eval_or_match true [e] fuel' st' env' uu uu;
        | None => (st', Rerr (Rabort Rtype_error))
        };
      | false with do_app _ (refs st', ffi st') op (rev vs) => {
        | Some ((refs, ffi), r) => ({| refs := refs;
                                      ffi  := ffi;
                                      clock := clock st';
                                      next_type_stamp := next_type_stamp st' ;
                                      next_exn_stamp := next_exn_stamp st'
                                   |}, list_result r);
        | None => (st', Rerr (Rabort Rtype_error))
        };
      };
    | res => res;
    };

  eval_or_match true [ELog And e1 e2] fuel st env _ _
    with eval_or_match true [e1] fuel st env uu uu => {
    | (st', Rval (v::_)) => if val_beq v (Boolv true)
                          then eval_or_match true [e2] fuel st env uu uu
                          else if val_beq v (Boolv false)
                               then (st', Rval [v])
                               else (st', Rerr (Rabort Rtype_error));
    | res => res
    };

  eval_or_match true [ELog Or e1 e2] fuel st env _ _
    with eval_or_match true [e1] fuel st env uu uu => {
    | (st', Rval (v::_)) => if val_beq v (Boolv true)
                           then (st', Rval [v])
                           else if val_beq v (Boolv false)
                                then eval_or_match true [e2] fuel st env uu uu
                                else (st', Rerr (Rabort Rtype_error));
    | res => res
    };

  eval_or_match true [EIf c t e] fuel st env _ _
    with eval_or_match true [c] fuel st env uu uu => {
    | (st', Rval [v]) => if val_beq v ConvTrue
                        then eval_or_match true [t] fuel st' env uu uu
                        else if val_beq v ConvFalse
                             then eval_or_match true [e] fuel st' env uu uu
                             else (st', Rerr (Rabort Rtype_error))
    | (st', Rval _) => (st', Rerr (Rabort Rtype_error))
    | res => res
    };

  eval_or_match true [EMat e pes] fuel st env v ev
    with eval_or_match true [e] fuel st env uu uu => {
    | (st', Rval (v'::vs')) =>
        eval_or_match false pes fuel st' env v' bind_exn_v
    | res => res
    };

  eval_or_match true [ELet o e1 e2] fuel st env _ _
    with eval_or_match true [e1] fuel st env uu uu => {
    | (st', Rval [v]) =>
        eval_or_match true [e2] fuel st' (update_sev env (nsOptBind o v (sev env))) uu uu;
    | (st', Rval _) => (st', Rerr (Rabort Rtype_error));
    | res => res
    };

  eval_or_match true [ELetrec funs e] fuel st env _ _ =>
    if nodup_str (map (fun '(x,y,z) => x) funs)
    then eval_or_match true [e] fuel st (update_sev env (build_rec_env funs env (sev env))) uu uu
    else (st, Rerr (Rabort Rtype_error));

  eval_or_match true [ETannot e t] fuel st env _ _ => eval_or_match true [e] fuel st env uu uu;

  eval_or_match true [ELannot e l] fuel st env _ _ => eval_or_match true [e] fuel st env uu uu;

  eval_or_match false [] _ st _ _ err_v => (st, Rerr (Rraise err_v));

  eval_or_match false ((p,e)::pes') fuel st env matched_v err_v =>
    if nodup_str (pat_bindings p [])
    then (match pmatch (sec env) (refs st) p matched_v [] with
          | Match env_v' =>
            eval_or_match true [e] fuel st
                     {| sev := nsAppend (alist_to_ns env_v') (sev env);
                        sec := (sec env) |} uu uu
          | No_match => eval_or_match false pes' fuel st env matched_v err_v
          | Match_type_error => (st, Rerr (Rabort Rtype_error))
          end)
    else (st, Rerr (Rabort Rtype_error)).
Proof.
all:constructor; simp mutmeasure; simp size_exp; simp size_pes; try(lia).
rewrite size_exps_rev. lia.
specialize (size_exp_at_least_S e2). lia.
specialize (size_exp_at_least_S e1). lia.
Defined.

Lemma Forall''_app : forall (T : Type) (P : T -> Type) (l : list T) (a : T), Forall'' P l -> P a -> Forall'' P (l ++ [a]).
  intros.
  induction l.
  constructor.
  assumption.
  assumption.
  inv X.
  constructor.
  assumption.
  apply IHl.
  assumption.
Qed.

Lemma Forall''_rev : forall (T : Type) (P : T -> Type) (l : list T),
    Forall'' P l -> Forall'' P (rev l).
  intros.
  induction l.
  constructor.
  inv X.
  simpl.
  apply Forall''_app; auto.
Qed.

Lemma eval_or_match_sing : forall (e : exp) (f : nat) (st st' : state nat) (env : sem_env val) (vs : list val),
    eval_or_match true [e] f st env uu uu = (st', Rval vs) -> exists (v : val), vs = [v].
Proof.
  intros e f; revert e.
  induction f;
  induction e using exp_rect'; intros.

  - simp eval_or_match in H.
    destruct (eval_or_match true [e] 0 st env uu uu) eqn:H'.
    simpl in *.
    inv H.
    break_match.
    + apply IHe in H'. break_match.
      * destruct H'. inv H0.
      * inv H1.
    + inv H1.

  - simp eval_or_match in H.
    induction X;
      destruct (eval_or_match true [e] 0 st env uu uu) eqn:H'.
    + inv H. break_match.
      * inv H1. eapply IHe. apply H'.
      * break_match; inv H1.
        simp eval_or_match in H1.
        inv H1.
    +  inv H. break_match.
       * inv H1. eapply IHe. apply H'.
       * break_match; inv H1.
         destruct x.
         simpl in p.
         simp eval_or_match in H1.
         break_if; simpl in *.
         -- break_match; simpl in *.
            simpl in *.
            apply IHX. assumption.
            inv H1.
            eapply p.
            apply H1.
         -- inv H1.

  - simp eval_or_match in H.
    inv H. econstructor. reflexivity.

  - simp eval_or_match in H.
    destruct (do_con_check (sec env) o (Datatypes.length l)) eqn:H'.
    * simpl in *.
      destruct (eval_or_match true (rev l) 0 st env uu uu) eqn:H''.
      simpl in *.
      break_match; simpl in *.
      -- destruct (build_conv (sec env) o (rev l0)) eqn:H'''.
         ++ simpl in *. inv H. eauto.
         ++ simpl in *. inv H.
      -- inv H.
    * simpl in *. inv H.

  - simp eval_or_match in H.
    destruct (nsLookup ident_string_beq i (sev env)); inv H; eauto.

  - simp eval_or_match in H. simp eval_or_match in H.
    inv H.
    eauto.

  (* EApp *)
  - simp eval_or_match in H. inv H.

  - destruct lo; simp eval_or_match in H.
    + destruct (eval_or_match true [e1] 0 st env uu uu) eqn:H'.
      simpl in *.
      break_match.
      * break_match; inv H.
        -- eapply IHe1. apply H'.
        -- break_if.
           ++ eapply IHe2. apply H.
           ++ break_if; inv H; eauto.
      * inv H.
    + destruct (eval_or_match true [e1] 0 st env uu uu) eqn:H'.
      simpl in *.
      break_match.
      * break_match; inv H.
        -- eapply IHe1. apply H'.
        -- break_if.
           ++ inv H. eauto.
           ++ break_if; inv H; eauto.
      * inv H.

 (* EIf *)
 - simp eval_or_match in H.
   destruct (eval_or_match true [e1] 0 st env uu uu) eqn:H'; simpl in *.
   break_match; inv H;
     break_match; simpl in *; inv H;
     break_match; inv H;
     break_if; inv H.
   + eapply IHe2; apply H.
   + break_if; inv H;
        eapply IHe3; apply H.

(* EMat *)
 - simp eval_or_match in H.
   induction X; destruct (eval_or_match true [e] 0 st env uu uu) eqn:H'; simpl in *.
   + break_match; inv H.
     break_match; inv H.
     * eapply IHe. apply H'.
     * simp eval_or_match in H. inv H.
   + break_match; inv H.
     break_match. inv H.
     * eapply IHe. apply H'.
     * subst. destruct x. simpl in *. simp eval_or_match in H.
       break_if; inv H.
       break_match.
       -- eapply IHX. apply H2.
       -- inv H2.
       -- eapply p. apply H.

 (* ELet *)
 - simp eval_or_match in H.
   destruct (eval_or_match true [e1] 0 st env uu uu); simpl in *; break_match; simpl in *.
   + break_match; inv H.
     break_match; inv H.
     eapply IHe2. apply H2.
   + inv H.

(* ELetrec *)
 - simp eval_or_match in H.
   break_if.
   eapply IHe.
   apply H.
   inv H.

 - simp eval_or_match in H.

 - simp eval_or_match in H.

 - simp eval_or_match in H.
   destruct (eval_or_match true [e] (S f) st env uu uu) eqn:H'; simpl in *;
     break_match; inv H.
   break_match; inv H.
   eapply IHe. apply H'.

 - simp eval_or_match in H.
   induction X;
     destruct (eval_or_match true [e] (S f) st env uu uu) eqn:H'; simpl in *; break_match; inv H.
   + eapply IHe; apply H'.
   + break_match; simp eval_or_match in H; inv H.
   + auto.
   + break_match; simp eval_or_match in H1.
     destruct x. simpl in *. simp eval_or_match in H.
     break_if; inv H.
     break_match; simp eval_or_match in H1; inv H.

 - simp eval_or_match in H. inv H. econstructor. reflexivity.

 - simp eval_or_match in H.
   destruct (do_con_check (sec env) o (Datatypes.length l)); simpl in *; inv H.
   destruct (eval_or_match true (rev l) (S f) st env uu uu) eqn:H'; simpl in *.
   destruct r; inv H.
   destruct (build_conv (sec env) o (rev l0)); inv H; eauto.

 - simp eval_or_match in H.
   destruct (nsLookup ident_string_beq i (sev env)); simpl in *; inv H; eauto.

 - simp eval_or_match in H; simpl in *; inv H; eauto.

 - simp eval_or_match in H; simpl in *.
   destruct (eval_or_match true (rev l) f st env uu uu) eqn:H'; simpl in *.
   apply Forall''_rev in X.
   induction X.
   + break_match; simpl in *; inv H.
     * simp eval_or_match in H'. inv H'.
       destruct o; simpl in *; inv H.
       destruct w; simpl in *; inv H.
       destruct w; simpl in *; inv H.
       destruct w; simpl in *; inv H.
       destruct w; simpl in *; inv H.
   + destruct r.
     * Opaque do_opapp.
       Opaque do_app.
       destruct (op_beq o Opapp); simpl in *.
       destruct (do_opapp (rev l1)); simpl in *.
       destruct p0; simpl in *.
       eapply IHf. apply H.
       inv H.
       destruct (do_app nat (refs s, ffi s) o (rev l1)).
       simpl in *.
       destruct p0.
       destruct s0.
       destruct r.
       simpl in H.
       inv H.
       eauto.
       inv H.
       simpl in *. inv H.
     * inv H.

 - destruct lo; simp eval_or_match in H;
    destruct (eval_or_match true [e1] (S f) st env uu uu) eqn:H'; simpl in *; inv H; eauto;
     repeat (break_match; simpl in *; inv H; eauto).

 - simp eval_or_match in H.
   destruct (eval_or_match true [e1] (S f) st env uu uu) eqn:H'; simpl in *.
   repeat (break_match; simpl in *; inv H; eauto).

 - simp eval_or_match in H.
   destruct (eval_or_match true [e] (S f) st env uu uu) eqn:H'; simpl in *; inv H; eauto.
   induction X.
   + repeat (break_match; simpl in *; inv H; eauto). simp eval_or_match in H. inv H.
   + repeat (break_match; simpl in *; inv H; eauto).
     destruct x; simpl in *. simp eval_or_match in H.
     repeat (break_match; simpl in *; inv H; eauto).

 - simp eval_or_match in H.
   destruct (eval_or_match true [e1] (S f) st env uu uu); simpl in *.
   repeat (break_match; simpl in *; inv H; eauto).

 - simp eval_or_match in H.
   induction X.
   repeat (break_match; simpl in *; inv H; eauto).
   destruct x. destruct p0. simpl in *.
   break_match;
    break_match; eauto; inv H.

 - simp eval_or_match in H.

 - simp eval_or_match in H.

Qed.


Definition evaluate := fun l f st env => @eval_or_match true l f st env uu uu.

Fixpoint identity_to_string (i : ident modN varN) : string :=
  match i with
  | Short n => n
  | Long m i' => m ++ (identity_to_string i')
  end.

Fixpoint size_dec (d : dec) : nat :=
  match d with
  | Dlet _ _ _ => 1
  | Dletrec _ _ => 1
  | Dtype _ _ => 1
  | Dtabbrev _ _ _ _ => 1
  | Dexn _ _ _ => 1
  | Dmod _ ds => 1 + fold_left plus (List.map size_dec ds) O
  | Dlocal lds ds => 1 + fold_left plus (List.map size_dec ds) O + fold_left plus (List.map size_dec lds) O
  end.

Definition size_decs (ds : list dec) : nat := fold_left plus (map size_dec ds) O.

Lemma size_dec_min_1 : forall (d : dec), 1 <= size_dec d.
Proof.
 destruct d; simpl; lia.
Qed.


Equations? evaluate_decs (fuel : nat) (st : state nat) (env : sem_env val) (decl : list dec)
  : state nat * result (sem_env val) val by wf (size_decs decl) := {
    evaluate_decs _ st _ [] => (st, Rval empty_sem_env);

    evaluate_decs fuel st env (d1::d2::decl') =>
        match evaluate_decs fuel st env [d1] with
        | (st1, Rval env1) =>
          match evaluate_decs fuel st1 (extend_dec_env env1 env) (d2::decl') with
          | (st2, r) => (st2, combine_dec_result env1 r)
          end
        | res => res
        end;

    evaluate_decs fuel st env [Dlet locs p e] =>
        if nodup_str (pat_bindings p [])
        then match eval_or_match true [e] fuel st env uu uu with
             | (st', Rval v) =>
               (st', match pmatch (sec env) (refs st') p (hd (Conv None []) v) [] with
                     | Match new_vals => Rval {| sec := nsEmpty; sev := alist_to_ns new_vals |}
                     | No_match => Rerr (Rraise bind_exn_v)
                     | Match_type_error => Rerr (Rabort Rtype_error)
                     end)
             | (st', Rerr err) => (st', Rerr err)
             end
        else (st, Rerr (Rabort Rtype_error));

    evaluate_decs fuel st env [Dletrec locs funs] =>
        (st,
         if nodup_str (map (fun x => fst (fst x)) funs)
         then Rval {| sev := build_rec_env funs env nsEmpty; sec := nsEmpty |}
         else Rerr (Rabort Rtype_error));

    evaluate_decs fuel st env [Dtype locs tds] =>
        if unique_ctros_in_defs tds
        then (state_update_next_type_stamp st (next_type_stamp st + List.length tds),
              Rval {| sev := nsEmpty; sec := build_tdefs (next_type_stamp st) tds |})
        else (st, Rerr (Rabort Rtype_error));

    evaluate_decs fuel st env [Dtabbrev _ _ _ _] => (st, Rval {| sev := nsEmpty; sec := nsEmpty |});

    evaluate_decs fuel st env [Dexn locs cn ts] =>
      (state_update_next_exn_stamp st ((next_exn_stamp st) + 1),
       Rval {| sev := nsEmpty; sec := nsSing cn (length ts, ExnStamp (next_exn_stamp st)) |});

    evaluate_decs fuel st env [Dmod mn ds] =>
        match evaluate_decs fuel st env ds with
        | (st', Rval env') => (st', Rval {| sev := nsLift mn (sev env'); sec := nsLift mn (sec env') |})
        | res => res
        end;

    evaluate_decs fuel st env [Dlocal ds1 ds2] =>
        match evaluate_decs fuel st env ds1 with
        | (st1, Rval env1) =>
          evaluate_decs fuel st1 (extend_dec_env env1 env) ds2
        | res => res
        end

     }.
Proof.
  all:unfold size_decs; simpl; try(lia).

  - assert (fold_addition_lt : forall (l : list nat) (n m : nat), n < m -> n < fold_left plus l m).
    (induction l; intros n m H; try (specialize (IHl n (m+a))); simpl; lia).
    pose size_dec_min_1 as H.
    destruct d1; simpl;
      try (apply fold_addition_lt;
           specialize (size_dec_min_1 d2); lia).
  - assert (fold_addition_lt : forall (l : list nat) (m n : nat), m < m + n -> fold_left plus l m < fold_left plus l (m + n)).
    induction l; intros m n H.
    simpl; lia.
    simpl. rewrite <- (Nat.add_assoc m n a). rewrite (Nat.add_comm n a). rewrite (Nat.add_assoc m a n).
    apply IHl. lia.
    rewrite Nat.add_comm.
    apply fold_addition_lt.
    specialize (size_dec_min_1 d2).
    specialize (size_dec_min_1 d1).
    lia.
Defined.
