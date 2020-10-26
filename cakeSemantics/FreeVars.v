Require Import List.
Import ListNotations.
Require Import BinNums.
Require Import Strings.String.
Require Import ZArith.BinInt.

Require Import CakeSem.Utils.
Require Import CakeSem.Namespace.
Require Import CakeSem.CakeAST.

Fixpoint pattern_vars (p : pat) : list varN :=
  let fix pattern_list_vars (pl : list pat) : list varN :=
      match pl with
      | [] => []
      | p'::pl' => pattern_vars p' ++ pattern_list_vars pl'
      end
  in
  match p with
  (* | Pany | Plit _ => [] *)
  | Pvar v => [v]
  | Pcon cid pl => pattern_list_vars pl
  (* | Pref p' | Ptannot p' _ => pattern_vars p' *)
  end.

Fixpoint free_vars (e : exp) : list (ident modN varN) :=
  let fix free_vars_helper (e : exp) (bl : list (ident modN varN)) : list (ident modN varN) :=
      let fix pattern_match_free_vars (pes : list (pat * exp)) (bl : list (ident modN varN)) :=
          match pes with
          | [] => []
          | (p',e')::pes' => free_vars_helper e' (map Short (pattern_vars p') ++ bl) ++ pattern_match_free_vars pes' bl
          end
      in

      let fix exp_list_free_vars (es : list exp) (bl : list (ident modN varN)) :=
          match es with
          | [] => []
          | e'::es' => free_vars_helper e' bl ++ exp_list_free_vars es' bl
          end
      in

      let fix vvexp_list_free_vars (vves : list (varN * varN * exp)) (bl : list (ident modN varN)) :=
          match vves with
          | [] => []
          | (fname, vname,e')::vves' => free_vars_helper e' ((Short vname)::bl) ++ vvexp_list_free_vars vves' bl
          end
      in
      match e with
      (* | ERaise e' => free_vars_helper e' bl *)
      (* | EHandle e' pes => free_vars_helper e' bl ++ pattern_match_free_vars pes bl *)
      (* | ELit _ => [] *)
      | ECon cid es => exp_list_free_vars es bl
      | EVar id => if in_dec (fun i i' => ident_eq_dec _ _ string_dec string_dec i i' ) id bl
                  then []
                  else [id]
      | EFun var_name e' => free_vars_helper e' ((Short var_name)::bl)
      | EApp o es => exp_list_free_vars es bl
      (* | ELog o e1 e2 => free_vars_helper e1 bl ++ free_vars_helper e2 bl *)
      (* | EIf c t f => free_vars_helper c bl ++ free_vars_helper t bl ++ free_vars_helper f bl *)
      | EMat e' pes => free_vars_helper e' bl ++ pattern_match_free_vars pes bl
      (* | ELet opt_var_name e1 e2 => match opt_var_name with *)
      (*                             | None => free_vars_helper e1 bl ++ free_vars_helper e2 bl *)
      (*                             | Some name => free_vars_helper e1 bl ++ free_vars_helper e2 ((Short name)::bl) *)
      (*                             end *)
      (* | ELetrec vves e' => free_vars_helper e' (map (fun x => Short (fst (fst x))) vves ++ bl) ++ vvexp_list_free_vars vves bl *)
      (* | ETannot e' _ => free_vars_helper e' bl *)
      | ELannot e' _ => free_vars_helper e' bl
      end
  in
  free_vars_helper e [].

(* Shell of a function that may need be defined in the future *)
(* Fixpoint free_vars_dec (d : dec) : list (ident modN varN) := *)
(*   let FAKE := [] in *)
(*   let fix free_vars_helper (d : dec) (bl : list (ident modN varN)) : list (ident modN varN) := *)
(*       match d with *)
(*       | Dlet _ p e => FAKE *)
(*       | Dletrec _ vves => FAKE *)
(*       | Dtype _ td => FAKE *)
(*       | Dtabbrev _ tvarNs typeNs tast => FAKE *)
(*       | Dexn _ cn tasts => FAKE *)
(*       | Dmod mn ds => FAKE *)
(*       | Dlocal dls ds => FAKE *)
(*       end *)
(*   in free_vars_helper d []. *)
