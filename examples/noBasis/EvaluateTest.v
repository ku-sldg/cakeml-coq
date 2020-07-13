Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.

Require Import FFI.
Require Import CakeSem.Namespace.
Require Import CakeSem.CakeAST.
Require Import CakeSem.SemanticsAux.
Require Import CakeSem.Evaluate.

Require Import NoBasis.


Definition init_env : sem_env val := empty_sem_env.
Definition init_store := empty_store val.

Parameter A : Type.
Parameter init_ffi_st : ffi_state A.
Definition init_state := Build_state 0 init_store init_ffi_st 0 0.

Definition noBasisProg := evaluate_decs 100 init_state init_env [ dec_def_0
                                                                ; dec_def_1
                                                                ; dec_def_2
                                                                ; dec_def_3
                                                                ; dec_def_4
                                                                ; dec_def_5
                                                                ; dec_def_6
                                                                ; dec_def_7
                                                                ; dec_def_8
                                                                ; dec_def_9
                                                                ; dec_def_10
                                                                ].

Definition noBasisProg' := evaluate_decs 19 init_state init_env [ dec_def_0
                                                                ; dec_def_1
                                                                ; dec_def_2
                                                                ; dec_def_3
                                                                ; dec_def_4
                                                                ; dec_def_5
                                                                ; dec_def_6
                                                                ; dec_def_7
                                                                ; dec_def_8
                                                                ; dec_def_9
                                                                ].
(* This takes a long time but will eventually terminate *)
(* Eval cbv in noBasisProg. *)

Definition my_env :=   {|
         sev := [(Short "answer",
                 Conv (Some (TypeStamp "S" 0))
                   [Conv (Some (TypeStamp "S" 0))
                      [Conv (Some (TypeStamp "S" 0))
                         [Conv (Some (TypeStamp "S" 0)) [Conv (Some (TypeStamp "S" 0)) [Conv (Some (TypeStamp "O" 0)) []]]]]]);
                (Short "three",
                Conv (Some (TypeStamp "S" 0))
                  [Conv (Some (TypeStamp "S" 0)) [Conv (Some (TypeStamp "S" 0)) [Conv (Some (TypeStamp "O" 0)) []]]]);
                (Short "two",
                Conv (Some (TypeStamp "S" 0)) [Conv (Some (TypeStamp "S" 0)) [Conv (Some (TypeStamp "O" 0)) []]]);
                (Short "abs_minus",
                Recclosure
                  {|
                  sev := [(Short "minus",
                          Recclosure
                            {|
                            sev := [];
                            sec := [(Short "SubtrahendLargerThanMinuend", (0, ExnStamp 0));
                                   (Short "S", (1, TypeStamp "S" 0)); (Short "O", (0, TypeStamp "O" 0))] |}
                            [("minus", "x",
                             EFun "y"
                               (ELannot
                                  (EMat (ELannot (EVar (Short "y")) [0])
                                     [(Pcon (Some (Short "O")) [], ELannot (EVar (Short "x")) [0]);
                                     (Pcon (Some (Short "S")) [Pvar "yp"],
                                     ELannot
                                       (EMat (ELannot (EVar (Short "x")) [0])
                                          [(Pcon (Some (Short "O")) [],
                                           ELannot
                                             (ERaise (ELannot (ECon (Some (Short "SubtrahendLargerThanMinuend")) []) [0]))
                                             [0]);
                                          (Pcon (Some (Short "S")) [Pvar "xp"],
                                          ELannot
                                            (EApp Opapp
                                               [ELannot
                                                  (EApp Opapp
                                                     [ELannot (EVar (Short "minus")) [0]; ELannot (EVar (Short "xp")) [0]])
                                                  [0]; ELannot (EVar (Short "yp")) [0]]) [0])]) [0])]) [0]))] "minus");
                         (Short "minus",
                         Recclosure
                           {|
                           sev := [];
                           sec := [(Short "SubtrahendLargerThanMinuend", (0, ExnStamp 0));
                                  (Short "S", (1, TypeStamp "S" 0)); (Short "O", (0, TypeStamp "O" 0))] |}
                           [("minus", "x",
                            EFun "y"
                              (ELannot
                                 (EMat (ELannot (EVar (Short "y")) [0])
                                    [(Pcon (Some (Short "O")) [], ELannot (EVar (Short "x")) [0]);
                                    (Pcon (Some (Short "S")) [Pvar "yp"],
                                    ELannot
                                      (EMat (ELannot (EVar (Short "x")) [0])
                                         [(Pcon (Some (Short "O")) [],
                                          ELannot
                                            (ERaise (ELannot (ECon (Some (Short "SubtrahendLargerThanMinuend")) []) [0]))
                                            [0]);
                                         (Pcon (Some (Short "S")) [Pvar "xp"],
                                         ELannot
                                           (EApp Opapp
                                              [ELannot
                                                 (EApp Opapp
                                                    [ELannot (EVar (Short "minus")) [0]; ELannot (EVar (Short "xp")) [0]])
                                                 [0]; ELannot (EVar (Short "yp")) [0]]) [0])]) [0])]) [0]))] "minus")];
                  sec := [(Short "SubtrahendLargerThanMinuend", (0, ExnStamp 0)); (Short "S", (1, TypeStamp "S" 0));
                         (Short "O", (0, TypeStamp "O" 0))] |}
                  [("abs_minus", "x",
                   EFun "y"
                     (ELannot
                        (EHandle
                           (ELannot
                              (EApp Opapp
                                 [ELannot (EApp Opapp [ELannot (EVar (Short "minus")) [0]; ELannot (EVar (Short "x")) [0]])
                                    [0]; ELannot (EVar (Short "y")) [0]]) [0])
                           [(Pcon (Some (Short "SubtrahendLargerThanMinuend")) [],
                            ELannot
                              (EApp Opapp
                                 [ELannot (EApp Opapp [ELannot (EVar (Short "minus")) [0]; ELannot (EVar (Short "y")) [0]])
                                    [0]; ELannot (EVar (Short "x")) [0]]) [0])]) [0]))] "abs_minus");
                (Short "minus",
                Recclosure
                  {|
                  sev := [];
                  sec := [(Short "SubtrahendLargerThanMinuend", (0, ExnStamp 0)); (Short "S", (1, TypeStamp "S" 0));
                         (Short "O", (0, TypeStamp "O" 0))] |}
                  [("minus", "x",
                   EFun "y"
                     (ELannot
                        (EMat (ELannot (EVar (Short "y")) [0])
                           [(Pcon (Some (Short "O")) [], ELannot (EVar (Short "x")) [0]);
                           (Pcon (Some (Short "S")) [Pvar "yp"],
                           ELannot
                             (EMat (ELannot (EVar (Short "x")) [0])
                                [(Pcon (Some (Short "O")) [],
                                 ELannot (ERaise (ELannot (ECon (Some (Short "SubtrahendLargerThanMinuend")) []) [0])) [0]);
                                (Pcon (Some (Short "S")) [Pvar "xp"],
                                ELannot
                                  (EApp Opapp
                                     [ELannot
                                        (EApp Opapp [ELannot (EVar (Short "minus")) [0]; ELannot (EVar (Short "xp")) [0]])
                                        [0]; ELannot (EVar (Short "yp")) [0]]) [0])]) [0])]) [0]))] "minus");
                (Short "mult",
                Recclosure
                  {|
                  sev := [(Short "plus",
                          Recclosure
                            {| sev := []; sec := [(Short "S", (1, TypeStamp "S" 0)); (Short "O", (0, TypeStamp "O" 0))] |}
                            [("plus", "x",
                             EFun "y"
                               (ELannot
                                  (EMat (ELannot (EVar (Short "x")) [0])
                                     [(Pcon (Some (Short "O")) [], ELannot (EVar (Short "y")) [0]);
                                     (Pcon (Some (Short "S")) [Pvar "xp"],
                                     ELannot
                                       (ECon (Some (Short "S"))
                                          [EApp Opapp
                                             [ELannot
                                                (EApp Opapp
                                                   [ELannot (EVar (Short "plus")) [0]; ELannot (EVar (Short "xp")) [0]]) [0];
                                             ELannot (EVar (Short "y")) [0]]]) [0])]) [0]))] "plus")];
                  sec := [(Short "S", (1, TypeStamp "S" 0)); (Short "O", (0, TypeStamp "O" 0))] |}
                  [("mult", "x",
                   EFun "y"
                     (ELannot
                        (EMat (ELannot (EVar (Short "x")) [0])
                           [(Pcon (Some (Short "O")) [], ELannot (ECon (Some (Short "O")) []) [0]);
                           (Pcon (Some (Short "S")) [Pvar "xp"],
                           ELannot
                             (ELet (Some "z")
                                (ELannot
                                   (EApp Opapp
                                      [ELannot
                                         (EApp Opapp [ELannot (EVar (Short "mult")) [0]; ELannot (EVar (Short "xp")) [0]])
                                         [0]; ELannot (EVar (Short "y")) [0]]) [0])
                                (ELannot
                                   (EApp Opapp
                                      [ELannot
                                         (EApp Opapp [ELannot (EVar (Short "plus")) [0]; ELannot (EVar (Short "y")) [0]])
                                         [0]; ELannot (EVar (Short "z")) [0]]) [0])) [0])]) [0]))] "mult");
                (Short "plus2",
                Recclosure
                  {|
                  sev := [(Short "succ",
                          Closure
                            {| sev := []; sec := [(Short "S", (1, TypeStamp "S" 0)); (Short "O", (0, TypeStamp "O" 0))] |}
                            "x" (ELannot (ECon (Some (Short "S")) [EVar (Short "x")]) [0]));
                         (Short "plus",
                         Recclosure
                           {| sev := []; sec := [(Short "S", (1, TypeStamp "S" 0)); (Short "O", (0, TypeStamp "O" 0))] |}
                           [("plus", "x",
                            EFun "y"
                              (ELannot
                                 (EMat (ELannot (EVar (Short "x")) [0])
                                    [(Pcon (Some (Short "O")) [], ELannot (EVar (Short "y")) [0]);
                                    (Pcon (Some (Short "S")) [Pvar "xp"],
                                    ELannot
                                      (ECon (Some (Short "S"))
                                         [EApp Opapp
                                            [ELannot
                                               (EApp Opapp
                                                  [ELannot (EVar (Short "plus")) [0]; ELannot (EVar (Short "xp")) [0]]) [0];
                                            ELannot (EVar (Short "y")) [0]]]) [0])]) [0]))] "plus")];
                  sec := [(Short "S", (1, TypeStamp "S" 0)); (Short "O", (0, TypeStamp "O" 0))] |}
                  [("plus2", "x",
                   EFun "y"
                     (ELannot
                        (EMat (ELannot (EVar (Short "x")) [0])
                           [(Pcon (Some (Short "O")) [], ELannot (EVar (Short "y")) [0]);
                           (Pcon (Some (Short "S")) [Pvar "xp"],
                           ELannot
                             (EApp Opapp
                                [ELannot (EVar (Short "succ")) [0];
                                ELannot
                                  (EApp Opapp
                                     [ELannot
                                        (EApp Opapp [ELannot (EVar (Short "plus")) [0]; ELannot (EVar (Short "xp")) [0]])
                                        [0]; ELannot (EVar (Short "y")) [0]]) [0]]) [0])]) [0]))] "plus2");
                (Short "plus",
                Recclosure {| sev := []; sec := [(Short "S", (1, TypeStamp "S" 0)); (Short "O", (0, TypeStamp "O" 0))] |}
                  [("plus", "x",
                   EFun "y"
                     (ELannot
                        (EMat (ELannot (EVar (Short "x")) [0])
                           [(Pcon (Some (Short "O")) [], ELannot (EVar (Short "y")) [0]);
                           (Pcon (Some (Short "S")) [Pvar "xp"],
                           ELannot
                             (ECon (Some (Short "S"))
                                [EApp Opapp
                                   [ELannot
                                      (EApp Opapp [ELannot (EVar (Short "plus")) [0]; ELannot (EVar (Short "xp")) [0]]) [0];
                                   ELannot (EVar (Short "y")) [0]]]) [0])]) [0]))] "plus");
                (Short "succ",
                Closure {| sev := []; sec := [(Short "S", (1, TypeStamp "S" 0)); (Short "O", (0, TypeStamp "O" 0))] |} "x"
                  (ELannot (ECon (Some (Short "S")) [EVar (Short "x")]) [0]))];
         sec := [(Short "SubtrahendLargerThanMinuend", (0, ExnStamp 0)); (Short "S", (1, TypeStamp "S" 0));
                (Short "O", (0, TypeStamp "O" 0))] |}.

Definition my_st := {| clock := 0; refs := []; ffi := init_ffi_st; next_type_stamp := 1; next_exn_stamp := 1 |}.

Inductive nat_rel_cake_nat (typestamp : nat) : nat -> val -> Prop :=
| zero_rel : nat_rel_cake_nat typestamp 0 (Conv (Some (TypeStamp "O" typestamp)) [])
| suc_rel  : forall (n : nat) (prev : val), nat_rel_cake_nat typestamp n prev -> nat_rel_cake_nat typestamp (S n) (Conv (Some (TypeStamp "S" typestamp)) [prev]).

Theorem plus_vs_cake_plus : forall (m n t : nat) (m_exp n_exp : exp) (m_val n_val m_n_val : val),
    (exists (mf : nat), evaluate_opt my_st my_env [m_exp] mf = (my_st, Rval [m_val])) ->
    (exists (nf : nat), evaluate_opt my_st my_env [n_exp] nf = (my_st, Rval [n_val])) ->
    nat_rel_cake_nat t m m_val ->
    nat_rel_cake_nat t n n_val ->
    (exists (mnf : nat), evaluate_opt my_st my_env [(EApp (Opapp) ((EApp (Opapp) ((EVar (Short ("plus"%string)))::m_exp::nil))::n_exp::nil))] mnf =
    (my_st, Rval [m_n_val])) ->
    nat_rel_cake_nat t (m+n) m_n_val.
Proof.
  intros m n t m_exp n_exp m_val n_val m_n_val.
Abort.
