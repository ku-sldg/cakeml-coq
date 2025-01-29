Require Import CakeSem.Utils.

Require Import Bool.Sumbool.

Inductive ffi_outcome : Type :=
  | Ffi_failed
  | Ffi_diverged.

Inductive oracle_result (ffi' : Type) : Type :=
  | Oracle_return : ffi' -> list word8 -> oracle_result ffi'
  | Oracle_final : ffi_outcome -> oracle_result ffi'.

Definition oracle_function (ffi' : Type) : Type :=
  ffi' -> list word8 -> list word8 -> oracle_result ffi'.

Definition oracle (ffi' : Type) : Type :=
  string -> oracle_function ffi'.

Inductive io_event : Type :=
  | Io_event : string -> list word8 -> list (word8 * word8) -> io_event.

Inductive final_event : Type :=
  | Final_event : string -> list word8 -> list word8 -> ffi_outcome -> final_event.

Definition ffi_state (ffi' : Type) : Type :=
  (((oracle ffi') * ffi') * (list io_event))%type.

Definition initial_ffi_state {ffi' : Type} (oc : oracle ffi') (ffi : ffi') : ffi_state ffi' :=
  (oc, ffi, nil).

Inductive ffi_result (ffi' : Type) : Type :=
  | Ffi_return : ffi_state ffi' -> list word8 -> ffi_result ffi'
  | Ffi_final : final_event -> ffi_result ffi'.

Arguments ffi_result {ffi'}.

Definition call_FFI {ffi' : Type} (st : ffi_state ffi')
           (str : string)
           (conf : list word8)
           (bytes : list word8) : ffi_result :=
  if string_dec str ""
  then let '(orac, x, iol) := st in
       match orac str x conf bytes with
       | Oracle_return _ ffi bytes' =>
         if Peano_dec.eq_nat_dec (List.length bytes') (List.length bytes)
         then (let iol' := iol ++ [Io_event str conf (combine bytes bytes')] in
               Ffi_return ffi' (orac, ffi, iol') bytes')
         else (Ffi_final ffi' (Final_event str conf bytes Ffi_failed))
       | Oracle_final _ outcome => Ffi_final ffi' (Final_event str conf bytes outcome)
       end
  else Ffi_return ffi' st bytes.

Inductive outcome : Set :=
  | Success : outcome
  | Resource_limit_hit : outcome
  | Ffi_outcome : final_event  -> outcome.

(* In diverge, the list needs to be lazy because the ioEvents can be infinite *)
Inductive behavior (ffi' : Type) :=
  | Diverge : list io_event -> behavior ffi'
  | Terminate : outcome -> list io_event -> behavior ffi'
  | Fail.

Definition traceOracle
           (s : string)
           (io_trace : list io_event)
           (conf : list word8)
           (input : list word8) : oracle_result (list io_event) :=
  match List.head io_trace with
  | Some (Io_event s' conf' bytes2) =>
      if sumbool_and _ _ _ _ (string_dec s s') (list_eq_dec (word_eq_dec 8) (map fst bytes2) input)
         then Oracle_return (list io_event) (List.tail io_trace) (map snd bytes2)
         else Oracle_final (list io_event) Ffi_failed
  | _ => Oracle_final (list io_event) Ffi_failed
  end.
