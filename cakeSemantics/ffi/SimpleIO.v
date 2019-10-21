From TLC Require Import LibLogic.
Require Import Coq.Lists.List.
Require Import Arith.Peano_dec.
Import ListNotations.
Require Import String.
Require Import FFI.
Require Import CakeSem.Utils.

Definition simpleIO  : Type :=
  ((list word8) * (list word8)).

Definition isEof
           (st : simpleIO)
           (conf : list word8)
           (input : list word8) : oracle_result simpleIO :=
  match input with
  | [] => Oracle_final simpleIO Ffi_failed
  | x :: xs => 
      let x' := nat_to_word 8 (If fst st = [] then 1%nat else 0%nat) in
      Oracle_return simpleIO st (x'::xs)
  end.

Definition getChar
           (st : simpleIO)
           (conf : list word8)
           (input : list word8) : oracle_result simpleIO :=
  match input with
  | [] => Oracle_final simpleIO Ffi_failed
  | x :: xs => match head (fst st) with
              | Some y => Oracle_return simpleIO (tail (fst st), snd st) (y :: xs)
              | _ => Oracle_final simpleIO Ffi_failed
              end
  end.

Definition putChar
           (st : simpleIO)
           (conf : list word8)
           (input : list word8) : oracle_result simpleIO :=
  match input with
  | [] => Oracle_final simpleIO Ffi_failed
  | x :: _ => Oracle_return simpleIO (fst st, x::(snd st)) input
  end.

Definition exit (st : simpleIO) (conf : list word8) (input : list word8) : oracle_result simpleIO
  := Oracle_final simpleIO Ffi_diverged.

Definition simpleIO_oracle (s : string) (st : simpleIO)
           (conf : list word8) (input : list word8) : oracle_result simpleIO :=
  If s = "isEof"
    then isEof st conf input
  else If s = "getChar"
    then getChar st conf input
  else If s = "putChar"
    then putChar st conf input
  else If s = "exit"
    then exit st conf input
  else
    Oracle_final simpleIO Ffi_failed.
