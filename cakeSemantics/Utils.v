Require Export String.
Require Export Coq.Lists.List.
Export ListNotations.
Require Export ZArith.BinInt.
Require Import Coq.Arith.PeanoNat.
Require Coq.Strings.Ascii.

(* From TLC Require Export LibString. (* almost same as [Export String] *) *)
(* From TLC Require Export LibInt. (* exports type [int] *) *)
(* From TLC Require Export LibList. *)

Require Export TLCbuffer. (* For local extensions to TLC *)

(* Export LibList_Notation. (* Notations [] and [x] and [x;y] *) *)

(* Require Ascii. (* To define type [char] *) *)

Require Export CakeSem.Word.

(** Abbreviation for types *)

Definition int := Z.
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
  list_char_to_string (List.map word8_to_char ls).

(** List update function *)
Fixpoint update {X : Type} (n : nat) (e : X) (l : list X) : list X :=
  match l with
  | [] => []
  | x::l' => match n with
           | O => e::l'
           | S n' => x::(update n' e l')
           end
  end.

(** DecidableEquality Hint DB to be used by subsequent theories *)
Create HintDb DecidableEquality.
Hint Resolve string_dec : DecidableEquality.
Hint Resolve Ascii.ascii_dec : DecidableEquality.
Hint Resolve (word_eq_dec 8) : DecidableEquality.
Hint Resolve (word_eq_dec 64) : DecidableEquality.
Hint Resolve Z.eq_dec : DecidableEquality.
Hint Resolve list_eq_dec : DecidableEquality.
Hint Resolve Peano_dec.eq_nat_dec : DecidableEquality.

Ltac inv H := inversion H; subst; clear H.

Theorem option_eq_dec : forall (X : Type), (forall (x y : X), {x = y} + {x <> y})
                                      -> (forall (xo yo : option X), {xo = yo} + {xo <> yo}).
Proof.
  decide equality.
Defined.
Hint Resolve option_eq_dec : DecidableEquality.

Theorem pair_eq_dec : forall (X Y: Type),
    (forall (x0 y0 : X), {x0 = y0} + {x0 <> y0}) ->
    (forall (x1 y1 : Y), {x1 = y1} + {x1 <> y1}) ->
    (forall (xp yp : X * Y), {xp = yp} + {xp <> yp}).
Proof.
  decide equality.
Defined.
Hint Resolve pair_eq_dec : DecidableEquality.

Theorem NoDuplicates_dec {A : Type} :
    (forall (x y : A), {x = y} + {x <> y}) -> forall (l : list A), {NoDup l} + {~ NoDup l}.
Proof.
  intros H l.
  induction l.
  - left; constructor.
  - destruct (in_dec H a l).
    right. intro contra. inversion contra; subst. apply (H2 i).
    destruct IHl.
    left; constructor; assumption.
    right. intro contra. inversion contra; subst. apply (n0 H3).
Defined.
