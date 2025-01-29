Require Import List.
Import ListNotations.
Require Import String.
Require Import ZArith.
Require Import Ascii.

Require Import CakeSem.Namespace.
Require Import CakeSem.ffi.FFI.
Require Import CakeSem.CakeAST.

Definition dec_def_0 := Dtype [(0%nat)] (((pair (pair (nil) ("nat"%string) ) ((pair ("O"%string) (nil))::(pair ("S"%string) ((Atapp (nil) (Short ("nat"%string)))::nil))::nil))::nil)).

Definition dec_def_1 := Dletrec [(0%nat)] ((pair (pair ("plus"%string) ("x"%string) ) (EFun ("y"%string) (ELannot (EMat (ELannot (EVar (Short ("x"%string))) [(0%nat)]) ((pair (Pcon (Some (Short ("O"%string))) (nil)) (ELannot (EVar (Short ("y"%string))) [(0%nat)]))::(pair (Pcon (Some (Short ("S"%string))) ((Pvar ("xp"%string))::nil)) (ELannot (ECon (Some (Short ("S"%string))) ((EApp (Opapp) ((ELannot (EApp (Opapp) ((ELannot (EVar (Short ("plus"%string))) [(0%nat)])::(ELannot (EVar (Short ("xp"%string))) [(0%nat)])::nil)) [(0%nat)])::(ELannot (EVar (Short ("y"%string))) [(0%nat)])::nil))::nil)) [(0%nat)]))::nil)) [(0%nat)])))::nil).

Definition dec_def_2 := Dlet [(0%nat)] (Pvar ("two"%string)) (ELannot (ECon (Some (Short ("S"%string))) ((ECon (Some (Short ("S"%string))) ((ECon (Some (Short ("O"%string))) (nil))::nil))::nil)) [(0%nat)]).

Definition dec_def_3 := Dlet [(0%nat)] (Pvar ("three"%string)) (ELannot (ECon (Some (Short ("S"%string))) ((EVar (Short ("two"%string)))::nil)) [(0%nat)]).

Definition dec_def_4 := Dlet [(0%nat)] (Pvar ("answer"%string)) (ELannot (EApp (Opapp) ((ELannot (EApp (Opapp) ((ELannot (EVar (Short ("plus"%string))) [(0%nat)])::(ELannot (EVar (Short ("two"%string))) [(0%nat)])::nil)) [(0%nat)])::(ELannot (EVar (Short ("three"%string))) [(0%nat)])::nil)) [(0%nat)]).

Definition prog := [dec_def_0; dec_def_1; dec_def_2; dec_def_3; dec_def_4].


