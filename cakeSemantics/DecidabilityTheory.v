Require Import String.
Require Import ZArith.
Require Import List.

Require Import Word.
Require Import Utils.
Require Import Namespace.
Require Import CakeAST.



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
Qed.
Hint Resolve option_eq_dec : DecidableEquality.

Theorem pair_eq_dec : forall (X Y: Type),
    (forall (x0 y0 : X), {x0 = y0} + {x0 <> y0}) ->
    (forall (x1 y1 : Y), {x1 = y1} + {x1 <> y1}) ->
    (forall (xp yp : X * Y), {xp = yp} + {xp <> yp}).
Proof.
  decide equality.
Qed.
Hint Resolve pair_eq_dec : DecidableEquality.

Theorem ident_eq_dec : forall (X Y : Type) (i0 i1 : ident X Y),
    (forall (x0 x1 : X), {x0 = x1} + {x0 <> x1}) ->
    (forall (y0 y1 : Y), {y0 = y1} + {y0 <> y1}) -> {i0 = i1} + {i0 <> i1}.
Proof. decide equality.  Qed.
Hint Resolve ident_eq_dec : DecidableEquality.

Section NamespaceDec.
  Variable M : Type.
  Variable N : Type.
  Variable V : Type.
  Hypothesis HM : forall (m0 m1 : M), {m0 = m1} + {m0 <> m1}.
  Hypothesis HN : forall (n0 n1 : N), {n0 = n1} + {n0 <> n1}.
  Hypothesis HV : forall (v0 v1 : V), {v0 = v1} + {v0 <> v1}.

  Theorem namespace_eq_dec : forall (n0 n1 : namespace M N V), {n0 = n1} + {n0 <> n1}.
  Proof. decide equality. decide equality. apply ident_eq_dec. apply HM. apply HN.  Qed.
End NamespaceDec.
Hint Resolve namespace_eq_dec : DecidableEquality.

Theorem lit_eq_dec (l l' : lit) : {l = l'} + {l <> l'}.
  decide equality; auto with DecidableEquality.  Qed.
Hint Resolve lit_eq_dec : DecidableEquality.

Theorem opn_eq_dec (o o' : opn) : {o = o'} + {o <> o'}.
 decide equality. Qed.
Hint Resolve opn_eq_dec : DecidableEquality.

Theorem opb_eq_dec (o o' : opn) : {o = o'} + {o <> o'}.
  decide equality.
Qed.
Hint Resolve opb_eq_dec : DecidableEquality.

Theorem opw_eq_dec (o o' : opn) : {o = o'} + {o <> o'}.
  decide equality.
Qed.
Hint Resolve opw_eq_dec : DecidableEquality.

Theorem shift_eq_dec (o o' : opn) : {o = o'} + {o <> o'}.
  decide equality.
Qed.
Hint Resolve shift_eq_dec : DecidableEquality.

Theorem op_eq_dec : forall (o0 o1 : op), {o0 = o1} + {o0 <> o1}.
Proof. repeat decide equality.  Qed.
Hint Resolve op_eq_dec : DecidableEquality.

Theorem lop_eq_dec : forall (l0 l1 : lop), {l0 = l1} + {l0 <> l1}.
Proof. decide equality.  Qed.
Hint Resolve lop_eq_dec : DecidableEquality.

Theorem ast_t_eq_dec : forall (a1 a2 : ast_t), {a1 = a2} + {a1 <> a2}.
Proof.
  decide equality; auto with DecidableEquality; try (apply ident_eq_dec; apply string_dec);
  generalize dependent l0;
  induction H; destruct l0;
    try (left; reflexivity);
    try (right; discriminate);
    try (destruct (p a);
         destruct (IHForall'' l0);
         try (inversion e0);
         try (right; intro con; injection con; contradiction);
         rewrite e; left; reflexivity).
Qed.
Hint Resolve ast_t_eq_dec : DecidableEquality.

Theorem constr_id_eq_dec : forall (c0 c1 : constr_id), {c0 = c1} + {c0 <> c1}.
Proof.
  decide equality. auto with DecidableEquality.  Qed.
Hint Resolve constr_id_eq_dec : DecidableEquality.

Theorem pat_eq_dec : forall (p0 p1 : pat), {p0 = p1} + {p0 <> p1}.
Proof. decide equality; auto with DecidableEquality.
       generalize dependent l0.
         induction l; destruct l0; try (left; reflexivity); try (right; discriminate).
       inv X.
       destruct (X0 p); subst.
       destruct (IHl X1 l0); subst.
       - left; reflexivity.
       - right; intro con; inversion con; auto.
       - right; intro con; inversion con; auto.
Qed.
Hint Resolve pat_eq_dec : DecidableEquality.

Theorem typeDef_eq_dec : forall (t0 t1 : typeDef), {t0 = t1} + {t0 <> t1}.
Proof. decide equality. decide equality.
       apply list_eq_dec; decide equality; auto with DecidableEquality.
       auto with DecidableEquality.  Qed.
Hint Resolve typeDef_eq_dec : DecidableEquality.

Theorem locs_eq_dec : forall (l0 l1 : locs), {l0 = l1} + {l0 <> l1}.
Proof.
  decide equality.
  auto with DecidableEquality.
Qed.
Hint Resolve locs_eq_dec : DecidableEquality.

Theorem exp_eq_dec : forall (e0 e1 : exp), {e0 = e1} + {e0 <> e1}.
Proof.
  decide equality; auto with DecidableEquality;
    try (decide equality; try (apply ident_eq_dec); apply string_dec); generalize dependent l0.

  induction X0; destruct l0.
  - left; reflexivity.
  - right; discriminate.
  - right; discriminate.
  - destruct x; destruct p0; simpl in *.
    destruct (pat_eq_dec p1 p0); destruct (p e4); destruct (IHX0 l0); subst;
      try (right; injection; auto); (left; reflexivity).
  - induction X; destruct l0; try (left; reflexivity); try (right; discriminate).
    destruct (p e); destruct (IHX l0); subst; try (right; injection; auto); left; reflexivity.
  - induction X; destruct l0; try (left; reflexivity); try (right; discriminate).
    destruct (p e); destruct (IHX l0); subst; try (right; injection; auto); left; reflexivity.
  - induction X0; destruct l0; try (left; reflexivity); try (right; discriminate).
    destruct x; destruct p0; simpl in *.
    destruct (p e4); destruct (pat_eq_dec p1 p0); destruct (IHX0 l0); subst;
      try (right; injection; auto); left; reflexivity.
  - induction X; destruct l0; try (left; reflexivity); try (right; discriminate).
    destruct x as [x' xe]; destruct x' as [xv0 xv1];
      destruct p0 as [p0' p0e]; destruct p0' as [p0v0 p0v1]; simpl in *.
    destruct (p p0e); destruct (string_dec xv0 p0v0); destruct (string_dec xv1 p0v1); destruct (IHX l0); subst;
      try (right; injection; auto); left; reflexivity.
Qed.
Hint Resolve exp_eq_dec : DecidableEquality.

Theorem dec_eq_dec : forall (d0 d1 : dec), {d0 = d1} + {d0 <> d1}.
Proof.
  decide equality; try (auto with DecidableEquality).
  - generalize dependent l0. induction X; destruct l0; try (left; reflexivity); try (right; discriminate).
    destruct (p d); destruct (IHX l0); subst; try (right; injection; auto); left; reflexivity.
  - generalize dependent l2. induction X0; destruct l2; try (left; reflexivity); try (right; discriminate).
    destruct (p d); destruct (IHX0 l2); subst; try (right; injection; auto); left; reflexivity.
  - generalize dependent l; induction X.
    + destruct l.
      * left; reflexivity.
      * right; discriminate.
    + destruct l0.
      * right; discriminate.
      * destruct (p d); destruct (IHX l0); subst; try (right; injection; auto); left; reflexivity.
Qed.
Hint Resolve dec_eq_dec : DecidableEquality.
