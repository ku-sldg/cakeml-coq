Set Implicit Arguments.
From TLC Require Import LibList.

(** File to put extensions to TLC *)

Module LibList_Notation.
Notation "[ ]" := nil (format "[ ]") : liblist_scope.
Notation "[ x ]" := (cons x nil) : liblist_scope.
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : liblist_scope.
Global Open Scope liblist_scope.
End LibList_Notation.

Fixpoint List_replicate A (n:nat) (x:A) : list A :=
  match n with
  | O => nil
  | S n' => x :: (List_replicate n' x)
  end.