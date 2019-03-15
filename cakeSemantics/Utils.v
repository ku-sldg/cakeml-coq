Require Import Ascii.
Require Import Classes.EquivDec.
Require Import Arith.
Import Bool.Sumbool.
Require Import List.
Import ListNotations.
Require Import String.
Require Import ZArith.BinInt.
Require Import CakeSem.Word.

Instance string_equiv_dec : EqDec string eq := string_dec.

Definition extract_bool (A B : Prop) (e : {A} + {B}) : bool :=
  match bool_of_sumbool e with
    exist _ b _ => b
  end.

Arguments extract_bool {A} {B} _.

Definition int := Z.
Definition char := ascii.
Definition word8 := word 8.
Definition word64 := word 64.

Definition word8_to_char (w : word8) : char :=
  match w with
  | Word _ n _ => ascii_of_nat n
  end.

Definition char_to_word8 (c : char) : word 8 :=
  let n := (nat_of_ascii c) in Word 8 (n mod 2 ^ 8) (Oneq 8 n).

(* int_to_word *)

Fixpoint string_to_list_char (str : string) : list char :=
  match str with
  | EmptyString => []
  | String c cs => c :: string_to_list_char cs
  end.

Fixpoint list_char_to_string (ls : list char) : string :=
  match ls with
  | [] => EmptyString
  | l :: ls' => String l (list_char_to_string ls')
  end.

Fixpoint list_word8_to_string (ls : list word8) : string :=
  match ls with
  | [] => EmptyString
  | l :: ls' => String (word8_to_char l) (list_word8_to_string ls')
 end.

Fixpoint allDistinct {A : Type} (f_dec : forall (x y : A), {x = y} + {x <> y}) (l : list A)
  : bool :=
  match l with
  | [] => true
  | h::t => andb (extract_bool (in_dec f_dec h t))
               (allDistinct f_dec t)
  end.
