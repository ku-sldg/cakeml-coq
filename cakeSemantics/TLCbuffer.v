Set Implicit Arguments.
From TLC Require Import LibList LibInt LibLogic.

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

Definition ListZ_replicate A (n:Z) (x:A) : list A :=
  If n < 0 then arbitrary else List_replicate (abs n) x.

