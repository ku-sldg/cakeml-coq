
(* The Word module should use the same definitions as CompCert.
   There is a functor that can be instantiated for the targeted word size.
   https://github.com/artart78/coq-bits/blob/master/test/integers.v
   See, e.g., the module Int64 defined in that file.
   If more flexibility on the word size is needed, e.g., to make all
   definitions parameteric in the word size, then let's discuss.
   For the moment, I won't touch your current Word module. *)


Require Import Arith.PeanoNat.
Require Import Omega.
Require Import ProofIrrelevance.

Inductive word (size : nat) : Type :=
| Word : forall n : nat, n < 2 ^ size -> word size.

Definition word_equality (s : nat) (w x : word s) : bool :=
  match w, x with
      | Word _ m _, Word _ n _ => beq_nat m n
  end.

Lemma word_eq_succ : forall (n0 n1 size : nat) (H0 : n0 < 2 ^ size) (H1 : n1 < 2 ^ size) (P0 : (S n0) < 2 ^ size) (P1 : (S n1) < 2 ^ size),
    Word size n0 H0 = Word size n1 H1 -> Word size (S n0) P0 = Word size (S n1) P1.
Proof.
  intros; generalize dependent P0; generalize dependent P1.
  inversion H.
  induction n0; destruct n1; try(inversion H3);intros;
    assert (P0 = P1) as P by apply proof_irrelevance; rewrite P; reflexivity.  Qed.

Lemma word_neq_nat_neq : forall m n s P Q, Word s m P <> Word s n Q -> m <> n.
Proof.
  induction m; destruct n; intros; try(discriminate).
  - assert (P = Q) by (apply proof_irrelevance; assumption).
    contradiction H. rewrite H0. reflexivity.
  - intro Cont; destruct Cont.
    assert (P = Q) by (apply proof_irrelevance; assumption). rewrite H0 in H. contradiction. Qed.

Lemma word_neq_succ : forall (n0 n1 size : nat) (H0 : n0 < 2 ^ size) (H1 : n1 < 2 ^ size) (P0 : (S n0) < 2 ^ size) (P1 : (S n1) < 2 ^ size),
    Word size n0 H0 <> Word size n1 H1 -> Word size (S n0) P0 <> Word size (S n1) P1.
Proof.
  induction n0; destruct n1; intros; try(discriminate).
  assert (H': H0 = H1) by apply proof_irrelevance; rewrite H' in H. contradiction.
  intros Con. inversion Con. apply word_neq_nat_neq in H.
  apply H. apply f_equal. assumption.  Qed.

Theorem word_eq_dec : forall (n : nat) (w1 w2 : word n), {w1 = w2} + {w1 <> w2}.
  intros size [n0 P0].
  induction n0; intros [n1 P1]; destruct n1; try(right; discriminate).
    + left. assert (P0 = P1) by apply proof_irrelevance. rewrite H. reflexivity.
    + assert (n0 < 2 ^ size) by (apply Nat.lt_succ_l;assumption).
      assert (n1 < 2 ^ size) by (apply Nat.lt_succ_l;assumption).
      assert ({Word size n0 H = Word size n1 H0} + {Word size n0 H <> Word size n1 H0}) by apply IHn0.
      inversion H1.
      * left. apply word_eq_succ with H H0. assumption.
      * right. apply word_neq_succ with H H0. assumption.  Qed.

Lemma lem0 : forall (m n p: nat), m < 2^p -> n < 2^p -> (m + n) mod (2 ^ p) < (2 ^ p) .
Proof.
  intros.
  apply Nat.mod_upper_bound.
  apply Nat.pow_nonzero.
  discriminate.
Qed.

Definition word_add (size : nat) (w1 w2 : word size) : word size :=
  match w1, w2 with
  | Word _ n1 P1, Word _ n2 P2 => Word size ((n1 + n2) mod 2 ^ size)
                                      (lem0 n1 n2 size P1 P2)
  end.

Fixpoint nat_sub_underflow (under : nat) (n m : nat) :=
  match n, m with
  | _, 0 => n
  | 0, S m' => nat_sub_underflow under under m'
  | S n', S m' => nat_sub_underflow under n' m'
  end.

Lemma lem4 : forall (m n p : nat), m < 2^p -> n < 2 ^ p ->
    nat_sub_underflow (2^p - 1) m n < (2^p).
Proof.
  intros m n p P Q.
  generalize dependent m.
  induction n; destruct m; auto; intros; simpl.
  - apply IHn.
    + apply (Nat.lt_trans n (S n) (2^p)) in Q.
      * assumption.
      * apply Nat.lt_succ_diag_r.
    + rewrite Nat.sub_succ_r.
      rewrite Nat.sub_0_r.
      apply Lt.lt_pred_n_n.
      assumption.
  - intros.
    apply IHn.
    + apply (Nat.lt_trans n (S n) (2^p)) in Q.
      * assumption.
      * apply Nat.lt_succ_diag_r.
    + apply (Nat.lt_trans m (S m) (2^p)) in P.
      * assumption.
      * apply Nat.lt_succ_diag_r.  Qed.

Definition word_sub (size : nat) (w1 w2 : word size) : word size :=
  match w1, w2 with
  | Word _ n1 P1, Word _ n2 P2 => Word size (nat_sub_underflow (2^size - 1) n1 n2)
                                     (lem4 n1 n2 size P1 P2)
  end.

Lemma bitwise_max_lem : forall (m n p : nat) (op : bool -> bool -> bool), m <= 2^p - 1 -> n <= 2^p - 1 ->
    (Nat.bitwise op p m n) <= 2^p - 1.
Proof.
  intros m n p. generalize dependent n.
  generalize dependent m. induction p; intros; auto.
  intros. simpl.
    assert (forall x y, x <= 2 ^ S y - 1 -> Nat.div2 x <= 2 ^ y - 1). {
      intros.
      destruct (Nat.Even_or_Odd x).
      * inversion H2. rewrite H3.
        rewrite Nat.div2_double.
        rewrite H3 in H1.
        assert (0 < 2) by omega.
        apply (Nat.mul_le_mono_pos_l _ _ 2 H4).
        rewrite  Nat.mul_sub_distr_l.
        rewrite <- H3.
        simpl (2 * 1).
        inversion H1.
        omega.
        omega.

      * inversion H2. rewrite H3.
        rewrite (Nat.add_comm).
        rewrite Nat.div2_succ_double.
        rewrite H3 in H1.
        inversion H1.
        omega.
        omega.
    }
    apply H1 in H.
    apply H1 in H0.
    apply (IHp _ _ op H) in H0.
    apply (Nat.mul_le_mono_pos_l _ _ 2) in H0.
    rewrite  Nat.mul_sub_distr_l in H0.
    simpl in *.
    destruct (op (Nat.odd m) (Nat.odd n)).
    simpl.
    apply le_n_S in H0.
    repeat rewrite (Nat.add_comm _ 0) in *.
    simpl in *.
    assert (forall x, S (2 ^ x + 2 ^ x - 2) = (2 ^ x + 2 ^ x - 1)). {
      intros.
      assert (2 <= 2 ^ x + 2 ^ x) by
          (induction x; simpl; omega).
      rewrite <- (Nat.sub_succ_l _ _ H2).
      reflexivity.
    }
    rewrite H2 in H0.
    apply H0.
    simpl.
    apply le_S in H0.
    repeat rewrite (Nat.add_comm _ 0) in *.
    simpl in *.
    assert (forall x, S (2 ^ x + 2 ^ x - 2) = (2 ^ x + 2 ^ x - 1)). {
      intros.
      assert (2 <= 2 ^ x + 2 ^ x) by
          (induction x; simpl; omega).
      rewrite <- (Nat.sub_succ_l _ _ H2).
      reflexivity.
    }
    rewrite H2 in H0.
    apply H0. omega.
Qed.

Theorem bitwise_max : forall (m n p : nat) (op : bool -> bool -> bool), m < 2^p -> n < 2^p ->
    (Nat.bitwise op p m n) < 2^p.
  intros.
  assert (2 ^ p = S ( 2 ^ p - 1)) by omega.
  rewrite H1 in *.
  apply le_lt_n_Sm.
  apply lt_n_Sm_le in H.
  apply lt_n_Sm_le in H0.
  apply bitwise_max_lem; assumption. Qed.

Definition word_and (size : nat) (w1 w2 : word size) : word size :=
  match w1, w2 with
  | Word _ n1 P1, Word _ n2 P2 => Word size (Nat.bitwise andb size n1 n2)
                                      (bitwise_max n1 n2 size andb P1 P2)
  end.

Definition word_or (size : nat) (w1 w2 : word size) : word size :=
  match w1, w2 with
  | Word _ n1 P1, Word _ n2 P2 => Word _ (Nat.bitwise orb size n1 n2)
                                      (bitwise_max n1 n2 size orb P1 P2)
  end.

Definition word_xor (size : nat) (w1 w2 : word size) : word size :=
  match w1, w2 with
  | Word _ n1 P1, Word _ n2 P2 => Word _ (Nat.bitwise xorb size n1 n2)
                                      (bitwise_max n1 n2 size xorb P1 P2)
  end.

Lemma Oneq : forall s n, n mod 2 ^ s < 2 ^ s.
Proof. intros. apply Nat.mod_upper_bound. apply Nat.pow_nonzero. discriminate.  Qed.

Definition word_to_nat (s : nat) (w : word s) : nat :=
  match w with | Word _ n _ => n end.

Definition nat_to_word (s n : nat) : word s :=
  Word s (n mod 2 ^ s) (Oneq s n).