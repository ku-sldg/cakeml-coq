Require Import CakeAST.
Require Import String.

(* This is a pretty printer for CakeML *)

Fixpoint pp_dec (d:dec) : string :=
  match d with
  | Dlet locs pat exp => "Dlet"
  | Dletrec locs lv => "Dletrec"
  | Dtype locs tydef => "Dtype"
  | Dtabbrev locs tvs tv ast => "Dtabbrev"
  | Dexn locs con asts => "Dexn"
  | Dmod mod decs => "Dmod"
  | Dlocal decs1 decs2 => "Dlocal"
  end.