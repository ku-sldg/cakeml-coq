Require Import List.
Import ListNotations.
Require Import String.
Require Import ZArith.
Require Import Ascii.

Require Import CakeSem.Namespace.
Require Import CakeSem.ffi.FFI.
Require Import CakeSem.CakeAST.

Definition dec_def_0 := Dtype [(0%nat)] (((pair (pair (nil) ("nat"%string) ) ((pair ("O"%string) (nil))::(pair ("S"%string) ((Atapp (nil) (Short ("nat"%string)))::nil))::nil))::nil)).

Definition dec_def_1 := Dlet [(0%nat)] (Pvar ("succ"%string)) (ELannot (EFun ("x"%string) (ELannot (ECon (Some (Short ("S"%string))) ((EVar (Short ("x"%string)))::nil)) [(0%nat)])) [(0%nat)]).

Definition dec_def_2 := Dletrec [(0%nat)] ((pair (pair ("plus"%string) ("x"%string) ) (EFun ("y"%string) (ELannot (EMat (ELannot (EVar (Short ("x"%string))) [(0%nat)]) ((pair (Pcon (Some (Short ("O"%string))) (nil)) (ELannot (EVar (Short ("y"%string))) [(0%nat)]))::(pair (Pcon (Some (Short ("S"%string))) ((Pvar ("xp"%string))::nil)) (ELannot (ECon (Some (Short ("S"%string))) ((EApp (Opapp) ((ELannot (EApp (Opapp) ((ELannot (EVar (Short ("plus"%string))) [(0%nat)])::(ELannot (EVar (Short ("xp"%string))) [(0%nat)])::nil)) [(0%nat)])::(ELannot (EVar (Short ("y"%string))) [(0%nat)])::nil))::nil)) [(0%nat)]))::nil)) [(0%nat)])))::nil).

Definition dec_def_3 := Dletrec [(0%nat)] ((pair (pair ("plus2"%string) ("x"%string) ) (EFun ("y"%string) (ELannot (EMat (ELannot (EVar (Short ("x"%string))) [(0%nat)]) ((pair (Pcon (Some (Short ("O"%string))) (nil)) (ELannot (EVar (Short ("y"%string))) [(0%nat)]))::(pair (Pcon (Some (Short ("S"%string))) ((Pvar ("xp"%string))::nil)) (ELannot (EApp (Opapp) ((ELannot (EVar (Short ("succ"%string))) [(0%nat)])::(ELannot (EApp (Opapp) ((ELannot (EApp (Opapp) ((ELannot (EVar (Short ("plus"%string))) [(0%nat)])::(ELannot (EVar (Short ("xp"%string))) [(0%nat)])::nil)) [(0%nat)])::(ELannot (EVar (Short ("y"%string))) [(0%nat)])::nil)) [(0%nat)])::nil)) [(0%nat)]))::nil)) [(0%nat)])))::nil).

Definition dec_def_4 := Dletrec [(0%nat)] ((pair (pair ("mult"%string) ("x"%string) ) (EFun ("y"%string) (ELannot (EMat (ELannot (EVar (Short ("x"%string))) [(0%nat)]) ((pair (Pcon (Some (Short ("O"%string))) (nil)) (ELannot (ECon (Some (Short ("O"%string))) (nil)) [(0%nat)]))::(pair (Pcon (Some (Short ("S"%string))) ((Pvar ("xp"%string))::nil)) (ELannot (ELet (Some ("z"%string)) (ELannot (EApp (Opapp) ((ELannot (EApp (Opapp) ((ELannot (EVar (Short ("mult"%string))) [(0%nat)])::(ELannot (EVar (Short ("xp"%string))) [(0%nat)])::nil)) [(0%nat)])::(ELannot (EVar (Short ("y"%string))) [(0%nat)])::nil)) [(0%nat)]) (ELannot (EApp (Opapp) ((ELannot (EApp (Opapp) ((ELannot (EVar (Short ("plus"%string))) [(0%nat)])::(ELannot (EVar (Short ("y"%string))) [(0%nat)])::nil)) [(0%nat)])::(ELannot (EVar (Short ("z"%string))) [(0%nat)])::nil)) [(0%nat)])) [(0%nat)]))::nil)) [(0%nat)])))::nil).

Definition dec_def_5 := Dexn [(0%nat)] ("SubtrahendLargerThanMinuend"%string) (nil).

Definition dec_def_6 := Dletrec [(0%nat)] ((pair (pair ("minus"%string) ("x"%string) ) (EFun ("y"%string) (ELannot (EMat (ELannot (EVar (Short ("y"%string))) [(0%nat)]) ((pair (Pcon (Some (Short ("O"%string))) (nil)) (ELannot (EVar (Short ("x"%string))) [(0%nat)]))::(pair (Pcon (Some (Short ("S"%string))) ((Pvar ("yp"%string))::nil)) (ELannot (EMat (ELannot (EVar (Short ("x"%string))) [(0%nat)]) ((pair (Pcon (Some (Short ("O"%string))) (nil)) (ELannot (ERaise (ELannot (ECon (Some (Short ("SubtrahendLargerThanMinuend"%string))) (nil)) [(0%nat)])) [(0%nat)]))::(pair (Pcon (Some (Short ("S"%string))) ((Pvar ("xp"%string))::nil)) (ELannot (EApp (Opapp) ((ELannot (EApp (Opapp) ((ELannot (EVar (Short ("minus"%string))) [(0%nat)])::(ELannot (EVar (Short ("xp"%string))) [(0%nat)])::nil)) [(0%nat)])::(ELannot (EVar (Short ("yp"%string))) [(0%nat)])::nil)) [(0%nat)]))::nil)) [(0%nat)]))::nil)) [(0%nat)])))::nil).

Definition dec_def_7 := Dletrec [(0%nat)] ((pair (pair ("abs_minus"%string) ("x"%string) ) (EFun ("y"%string) (ELannot (EHandle (ELannot (EApp (Opapp) ((ELannot (EApp (Opapp) ((ELannot (EVar (Short ("minus"%string))) [(0%nat)])::(ELannot (EVar (Short ("x"%string))) [(0%nat)])::nil)) [(0%nat)])::(ELannot (EVar (Short ("y"%string))) [(0%nat)])::nil)) [(0%nat)]) ((pair (Pcon (Some (Short ("SubtrahendLargerThanMinuend"%string))) (nil)) (ELannot (EApp (Opapp) ((ELannot (EApp (Opapp) ((ELannot (EVar (Short ("minus"%string))) [(0%nat)])::(ELannot (EVar (Short ("y"%string))) [(0%nat)])::nil)) [(0%nat)])::(ELannot (EVar (Short ("x"%string))) [(0%nat)])::nil)) [(0%nat)]))::nil)) [(0%nat)])))::nil).

Definition dec_def_8 := Dlet [(0%nat)] (Pvar ("two"%string)) (ELannot (ECon (Some (Short ("S"%string))) ((ECon (Some (Short ("S"%string))) ((ECon (Some (Short ("O"%string))) (nil))::nil))::nil)) [(0%nat)]).

Definition dec_def_9 := Dlet [(0%nat)] (Pvar ("three"%string)) (ELannot (ECon (Some (Short ("S"%string))) ((EVar (Short ("two"%string)))::nil)) [(0%nat)]).

Definition dec_def_10 := Dlet [(0%nat)] (Pvar ("answer"%string)) (ELannot (EApp (Opapp) ((ELannot (EApp (Opapp) ((ELannot (EVar (Short ("plus"%string))) [(0%nat)])::(ELannot (EVar (Short ("two"%string))) [(0%nat)])::nil)) [(0%nat)])::(ELannot (EVar (Short ("three"%string))) [(0%nat)])::nil)) [(0%nat)]).

Definition prog := [dec_def_0; dec_def_1; dec_def_2; dec_def_3; dec_def_4; dec_def_5; dec_def_6; dec_def_7; dec_def_8; dec_def_9; dec_def_10].


