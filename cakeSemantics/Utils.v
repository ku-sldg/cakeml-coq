From TLC Require Export LibInt. (* exports type [int] *)
From TLC Require Export LibList.

Require Export TLCbuffer.
Export LibList_Notation. (* notation [] and [x] *)

Require Ascii.
Require Import Arith.
Require Import String.
Require Import CakeSem.Word.

(** Comparison for strings -- TODO: will be removed later *)

Require Import Classes.EquivDec.
Instance string_equiv_dec : EqDec string eq := string_dec.

(** Abbreviation for types *)

Definition char := Ascii.ascii.
Definition word8 := word 8.
Definition word64 := word 64.

(** Conversion between [word8] and [char] *)

Definition word8_to_char (w : word8) : char :=
  match w with
  | Word _ n _ => Ascii.ascii_of_nat n
  end.

Definition char_to_word8 (c : char) : word8 :=
  let n := (Ascii.nat_of_ascii c) in 
  Word 8 (n mod 2 ^ 8) (Oneq 8 n).

(** Conversion between [string] and [list char]

    Remark: it would make so much more sense for [string] to be defined 
    as [list char]. The caveat for switching representation is that Coq 
    hardcodes the parsing at type [string]. *)

Fixpoint string_to_list_char (str : string) : list char :=
  match str with
  | EmptyString => nil
  | String c cs => c :: string_to_list_char cs
  end.

Fixpoint list_char_to_string (ls : list char) : string :=
  match ls with
  | nil => EmptyString
  | l :: ls' => String l (list_char_to_string ls')
  end.

(** Conversion between [string] and [list word8] *)

Definition list_word8_to_string (ls : list word8) : string :=
  list_char_to_string (LibList.map word8_to_char ls).
