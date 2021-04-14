Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
(* Require Import StructTact.StructTactics. *)
(* Require Import Omega. *)
(* Require Import Coq.Logic.Eqdep_dec. *)
(* Require Import Equations.Equations. *)

Require Import CakeSem.Utils.
Require Import FFI.
Require Import CakeSem.Namespace.
Require Import CakeSem.CakeAST.
Require Import CakeSem.SemanticsAux.
(* Require Import CakeSem.Evaluate. *)

(* Require Import BasisPlus. *)

Definition init_env : sem_env val := empty_sem_env.
Definition init_store := empty_store val.
Parameter init_ffi_st : ffi_state nat.
Definition init_state := Build_state 0 init_store init_ffi_st 0 0.

Definition st_0_26 := {|
  clock := 0;
  refs := init_store;
  ffi := init_ffi_st;
  next_type_stamp := 3;
  next_exn_stamp := 0 |}.

Open Scope Z_scope.
Definition env_0_26 := {|
  sev := [(Long "Option" (Short "compare"),
           Closure
             {|
             sev := [];
             sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Equal", (0%nat, TypeStamp "Equal" 1));
                    (Short "Some", (1%nat, TypeStamp "Some" 0));
                    (Short "Less", (0%nat, TypeStamp "Less" 1));
                    (Short "Some", (1%nat, TypeStamp "Some" 0));
                    (Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Greater", (0%nat, TypeStamp "Greater" 1));
                    (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v4"
             (EFun "v5"
                   (EFun "v6"
                         (EMat (EVar (Short "v5"))
                               [(Pcon (Some (Short "None")) [],
                                 EMat (EVar (Short "v6"))
                                      [(Pcon (Some (Short "None")) [], ECon (Some (Short "Equal")) []);
                                      (Pcon (Some (Short "Some")) [Pvar "v1"], ECon (Some (Short "Less")) [])]);
                               (Pcon (Some (Short "Some")) [Pvar "v3"],
                                EMat (EVar (Short "v6"))
                                     [(Pcon (Some (Short "None")) [], ECon (Some (Short "Greater")) []);
                                     (Pcon (Some (Short "Some")) [Pvar "v2"],
                                      EApp Opapp
                                           [EApp Opapp [EVar (Short "v4"); EVar (Short "v3")]; EVar (Short "v2")])])]))));
         (Long "Option" (Short "map2"),
          Closure
            {|
              sev := [(Short "isSome",
                       Closure
                         {|
                           sev := [];
                           sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                                  (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v2"
                         (EMat (EVar (Short "v2"))
                               [(Pcon (Some (Short "None")) [],
                                 EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]);
                               (Pcon (Some (Short "Some")) [Pvar "v1"],
                                EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)])]));
                     (Short "isSome",
                      Closure
                        {|
                          sev := [];
                          sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                                 (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v2"
                        (EMat (EVar (Short "v2"))
                              [(Pcon (Some (Short "None")) [],
                                EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]);
                              (Pcon (Some (Short "Some")) [Pvar "v1"],
                               EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)])]));
                     (Short "valOf",
                      Closure
                        {|
                          sev := [];
                          sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                                 (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "x0"
                        (EMat (EVar (Short "x0"))
                              [(Pcon (Some (Short "None")) [], ERaise (ECon (Some (Short "Bind")) []));
                              (Pcon (Some (Short "Some")) [Pvar "v1"], EVar (Short "v1"))]));
                     (Short "valOf",
                      Closure
                        {|
                          sev := [];
                          sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                                 (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "x0"
                        (EMat (EVar (Short "x0"))
                              [(Pcon (Some (Short "None")) [], ERaise (ECon (Some (Short "Bind")) []));
                              (Pcon (Some (Short "Some")) [Pvar "v1"], EVar (Short "v1"))]))];
              sec := [(Short "Some", (1%nat, TypeStamp "Some" 0));
                     (Short "None", (0%nat, TypeStamp "None" 0))] |} "v1"
            (EFun "v2"
                  (EFun "v3"
                        (EIf
                           (ELog And (EApp Opapp [EVar (Short "isSome"); EVar (Short "v2")])
                                 (EApp Opapp [EVar (Short "isSome"); EVar (Short "v3")]))
                           (ECon (Some (Short "Some"))
                                 [EApp Opapp
                                       [EApp Opapp
                                             [EVar (Short "v1");
                                             EApp Opapp [EVar (Short "valOf"); EVar (Short "v2")]];
                                       EApp Opapp [EVar (Short "valOf"); EVar (Short "v3")]]])
                           (ECon (Some (Short "None")) [])))));
         (Long "Option" (Short "isNone"),
          Closure
            {|
              sev := [];
              sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                     (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v2"
            (EMat (EVar (Short "v2"))
                  [(Pcon (Some (Short "None")) [], EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)]);
                  (Pcon (Some (Short "Some")) [Pvar "v1"],
                   EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)])]));
         (Long "Option" (Short "composePartial"),
          Closure
            {|
              sev := [];
              sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                     (Short "None", (0%nat, TypeStamp "None" 0));
                     (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v3"
            (EFun "v4"
                  (EFun "v2"
                        (EMat (EApp Opapp [EVar (Short "v4"); EVar (Short "v2")])
                              [(Pcon (Some (Short "None")) [], ECon (Some (Short "None")) []);
                              (Pcon (Some (Short "Some")) [Pvar "v1"],
                               EApp Opapp [EVar (Short "v3"); EVar (Short "v1")])]))));
         (Long "Option" (Short "compose"),
          Closure
            {|
              sev := [];
              sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                     (Short "None", (0%nat, TypeStamp "None" 0));
                     (Short "Some", (1%nat, TypeStamp "Some" 0));
                     (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v3"
            (EFun "v4"
                  (EFun "v2"
                        (EMat (EApp Opapp [EVar (Short "v4"); EVar (Short "v2")])
                              [(Pcon (Some (Short "None")) [], ECon (Some (Short "None")) []);
                              (Pcon (Some (Short "Some")) [Pvar "v1"],
                               ECon (Some (Short "Some")) [EApp Opapp [EVar (Short "v3"); EVar (Short "v1")]])]))));
         (Long "Option" (Short "mapPartial"),
          Closure
            {|
              sev := [];
              sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                     (Short "None", (0%nat, TypeStamp "None" 0));
                     (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v2"
            (EFun "v3"
                  (EMat (EVar (Short "v3"))
                        [(Pcon (Some (Short "None")) [], ECon (Some (Short "None")) []);
                        (Pcon (Some (Short "Some")) [Pvar "v1"],
                         EApp Opapp [EVar (Short "v2"); EVar (Short "v1")])])));
         (Long "Option" (Short "map"),
          Closure
            {|
              sev := [];
              sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                     (Short "None", (0%nat, TypeStamp "None" 0));
                     (Short "Some", (1%nat, TypeStamp "Some" 0));
                     (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v2"
            (EFun "v3"
                  (EMat (EVar (Short "v3"))
                        [(Pcon (Some (Short "None")) [], ECon (Some (Short "None")) []);
                        (Pcon (Some (Short "Some")) [Pvar "v1"],
                         ECon (Some (Short "Some")) [EApp Opapp [EVar (Short "v2"); EVar (Short "v1")]])])));
         (Long "Option" (Short "join"),
          Closure
            {|
              sev := [];
              sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                     (Short "None", (0%nat, TypeStamp "None" 0));
                     (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v2"
            (EMat (EVar (Short "v2"))
                  [(Pcon (Some (Short "None")) [], ECon (Some (Short "None")) []);
                  (Pcon (Some (Short "Some")) [Pvar "v1"], EVar (Short "v1"))]));
         (Long "Option" (Short "valOf"),
          Closure
            {|
              sev := [];
              sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                     (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "x0"
            (EMat (EVar (Short "x0"))
                  [(Pcon (Some (Short "None")) [], ERaise (ECon (Some (Short "Bind")) []));
                  (Pcon (Some (Short "Some")) [Pvar "v1"], EVar (Short "v1"))]));
         (Long "Option" (Short "isSome"),
          Closure
            {|
              sev := [];
              sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                     (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v2"
            (EMat (EVar (Short "v2"))
                  [(Pcon (Some (Short "None")) [], EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]);
                  (Pcon (Some (Short "Some")) [Pvar "v1"],
                   EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)])]));
         (Long "Option" (Short "getOpt"),
          Closure
            {|
              sev := [];
              sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                     (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v3"
            (EFun "v2"
                  (EMat (EVar (Short "v3"))
                        [(Pcon (Some (Short "None")) [], EVar (Short "v2"));
                        (Pcon (Some (Short "Some")) [Pvar "v1"], EVar (Short "v1"))])));
         (Long "Runtime" (Short "abort"),
          Recclosure
            {|
              sev := [(Short "exit",
                       Recclosure {| sev := []; sec := [] |}
                                  [("exit", "i",
                                    ELet (Some "y") (EApp (WordFromInt W8) [EVar (Short "i")])
                                         (ELet (Some "x") (EApp Aw8alloc [ELit (IntLit 1); EVar (Short "y")])
                                               (EApp (FFI "exit") [ELit (StrLit ""); EVar (Short "x")])))] "exit")];
              sec := [] |}
            [("abort", "u",
              EMat (EVar (Short "u"))
                   [(Pcon None [], EApp Opapp [EVar (Short "exit"); ELit (IntLit 1)])])] "abort");
         (Long "Runtime" (Short "exit"),
          Recclosure {| sev := []; sec := [] |}
                     [("exit", "i",
                       ELet (Some "y") (EApp (WordFromInt W8) [EVar (Short "i")])
                            (ELet (Some "x") (EApp Aw8alloc [ELit (IntLit 1); EVar (Short "y")])
                                  (EApp (FFI "exit") [ELit (StrLit ""); EVar (Short "x")])))] "exit");
         (Long "Runtime" (Short "debugMsg"),
          Closure {| sev := []; sec := [] |} "v1"
                  (EApp (FFI "")
                        [EVar (Short "v1");
                        EApp Aw8alloc [ELit (IntLit 0); ELit (Word8Lit (nat_to_word 8 0))]]));
         (Long "Runtime" (Short "fail"),
          Closure {| sev := []; sec := [] |} "v1"
                  (EMat (EVar (Short "v1"))
                        [(Pcon None [],
                          ELet (Some "a") (EVar (Short "v1"))
                               (ELet (Some "n") (ELit (StrLit "18446744073709551616"))
                                     (ELet None (EApp Aalloc [EVar (Short "n"); EVar (Short "n")]) (EVar (Short "a")))))]));
         (Long "Runtime" (Short "fullGC"),
          Closure {| sev := []; sec := [] |} "v1"
                  (EMat (EVar (Short "v1"))
                        [(Pcon None [], EApp ConfigGC [ELit (IntLit 0); ELit (IntLit 0)])]));
         (Short "repeat",
          Recclosure {| sev := []; sec := [] |}
                     [("repeat", "f",
                       EFun "x"
                            (ELet (Some "a") (EApp Opapp [EVar (Short "f"); EVar (Short "x")])
                                  (EApp Opapp
                                        [EApp Opapp [EVar (Short "repeat"); EVar (Short "f")]; EVar (Short "a")])))]
                     "repeat");
         (Short "least",
          Closure
            {|
              sev := [(Short "while",
                       Recclosure {| sev := []; sec := [] |}
                                  [("while", "v1",
                                    EFun "v2"
                                         (EFun "v3"
                                               (EIf (EApp Opapp [EVar (Short "v1"); EVar (Short "v3")])
                                                    (EApp Opapp
                                                          [EApp Opapp
                                                                [EApp Opapp [EVar (Short "while"); EVar (Short "v1")];
                                                                EVar (Short "v2")];
                                                          EApp Opapp [EVar (Short "v2"); EVar (Short "v3")]])
                                                    (EVar (Short "v3")))))] "while")];
              sec := [] |} "v3"
            (EApp Opapp
                  [EApp Opapp
                        [EApp Opapp
                              [EVar (Short "while");
                              EFun "v1"
                                   (EApp Equality
                                         [EApp Opapp [EVar (Short "v3"); EVar (Short "v1")];
                                         EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]])];
                        EFun "v2" (EApp (Opn Plus) [EVar (Short "v2"); ELit (IntLit 1)])];
                  ELit (IntLit 0)]));
         (Short "owhile",
          Recclosure {| sev := []; sec := [] |}
                     [("owhile", "v1",
                       EFun "v2"
                            (EFun "v3"
                                  (EIf (EApp Opapp [EVar (Short "v1"); EVar (Short "v3")])
                                       (EApp Opapp
                                             [EApp Opapp
                                                   [EApp Opapp [EVar (Short "owhile"); EVar (Short "v1")]; EVar (Short "v2")];
                                             EApp Opapp [EVar (Short "v2"); EVar (Short "v3")]])
                                       (ECon (Some (Short "Some")) [EVar (Short "v3")]))))] "owhile");
         (Short "while",
          Recclosure {| sev := []; sec := [] |}
                     [("while", "v1",
                       EFun "v2"
                            (EFun "v3"
                                  (EIf (EApp Opapp [EVar (Short "v1"); EVar (Short "v3")])
                                       (EApp Opapp
                                             [EApp Opapp
                                                   [EApp Opapp [EVar (Short "while"); EVar (Short "v1")]; EVar (Short "v2")];
                                             EApp Opapp [EVar (Short "v2"); EVar (Short "v3")]])
                                       (EVar (Short "v3")))))] "while");
         (Short "pre",
          Closure {| sev := []; sec := [] |} "v1"
                  (ELet (Some "k") (EApp (Opn Minus) [EVar (Short "v1"); ELit (IntLit 1)])
                        (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)]) (ELit (IntLit 0))
                             (EVar (Short "k")))));
         (Short "abs_diff",
          Closure {| sev := []; sec := [] |} "v2"
                  (EFun "v1"
                        (EIf (EApp (Opb Lt) [EVar (Short "v2"); EVar (Short "v1")])
                             (ELet (Some "k") (EApp (Opn Minus) [EVar (Short "v1"); EVar (Short "v2")])
                                   (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                        (ELit (IntLit 0)) (EVar (Short "k"))))
                             (ELet (Some "k") (EApp (Opn Minus) [EVar (Short "v2"); EVar (Short "v1")])
                                   (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                        (ELit (IntLit 0)) (EVar (Short "k")))))));
         (Short "funpow",
          Recclosure {| sev := []; sec := [] |}
                     [("funpow", "v1",
                       EFun "v2"
                            (EFun "v3"
                                  (EIf (EApp Equality [EVar (Short "v2"); ELit (IntLit 0)])
                                       (EVar (Short "v3"))
                                       (EApp Opapp
                                             [EApp Opapp
                                                   [EApp Opapp [EVar (Short "funpow"); EVar (Short "v1")];
                                                   ELet (Some "k") (EApp (Opn Minus) [EVar (Short "v2"); ELit (IntLit 1)])
                                                        (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                                             (ELit (IntLit 0)) (EVar (Short "k")))];
                                             EApp Opapp [EVar (Short "v1"); EVar (Short "v3")]]))))] "funpow");
         (Short "odd",
          Closure {| sev := []; sec := [] |} "v1"
                  (EApp (Opb Lt) [ELit (IntLit 0); EApp (Opn Modulo) [EVar (Short "v1"); ELit (IntLit 2)]]));
         (Short "even",
          Closure {| sev := []; sec := [] |} "v1"
                  (EApp Equality [EApp (Opn Modulo) [EVar (Short "v1"); ELit (IntLit 2)]; ELit (IntLit 0)]));
         (Short "max",
          Closure {| sev := []; sec := [] |} "v1"
                  (EFun "v2"
                        (EIf (EApp (Opb Lt) [EVar (Short "v1"); EVar (Short "v2")])
                             (EVar (Short "v2")) (EVar (Short "v1")))));
         (Short "min",
          Closure {| sev := []; sec := [] |} "v1"
                  (EFun "v2"
                        (EIf (EApp (Opb Lt) [EVar (Short "v1"); EVar (Short "v2")])
                             (EVar (Short "v1")) (EVar (Short "v2")))));
         (Short "exp",
          Closure
            {|
              sev := [(Short "exp",
                       Recclosure {| sev := []; sec := [] |}
                                  [("exp", "v2",
                                    EFun "v3"
                                         (EFun "v1"
                                               (EIf (EApp Equality [EVar (Short "v3"); ELit (IntLit 0)])
                                                    (EVar (Short "v1"))
                                                    (EApp Opapp
                                                          [EApp Opapp
                                                                [EApp Opapp [EVar (Short "exp"); EVar (Short "v2")];
                                                                ELet (Some "k")
                                                                     (EApp (Opn Minus) [EVar (Short "v3"); ELit (IntLit 1)])
                                                                     (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                                                          (ELit (IntLit 0)) (EVar (Short "k")))];
                                                          EApp (Opn Times) [EVar (Short "v2"); EVar (Short "v1")]]))))] "exp")];
              sec := [] |} "v1"
            (EFun "v2"
                  (EApp Opapp
                        [EApp Opapp [EApp Opapp [EVar (Short "exp"); EVar (Short "v1")]; EVar (Short "v2")];
                        ELit (IntLit 1)])));
         (Short "exp",
          Recclosure {| sev := []; sec := [] |}
                     [("exp", "v2",
                       EFun "v3"
                            (EFun "v1"
                                  (EIf (EApp Equality [EVar (Short "v3"); ELit (IntLit 0)])
                                       (EVar (Short "v1"))
                                       (EApp Opapp
                                             [EApp Opapp
                                                   [EApp Opapp [EVar (Short "exp"); EVar (Short "v2")];
                                                   ELet (Some "k") (EApp (Opn Minus) [EVar (Short "v3"); ELit (IntLit 1)])
                                                        (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                                             (ELit (IntLit 0)) (EVar (Short "k")))];
                                             EApp (Opn Times) [EVar (Short "v2"); EVar (Short "v1")]]))))] "exp");
         (Short "update",
          Closure {| sev := []; sec := [] |} "v3"
                  (EFun "v4"
                        (EFun "v2"
                              (EFun "v1"
                                    (EIf (EApp Equality [EVar (Short "v3"); EVar (Short "v1")])
                                         (EVar (Short "v4")) (EApp Opapp [EVar (Short "v2"); EVar (Short "v1")]))))));
         (Short "const", Closure {| sev := []; sec := [] |} "v2" (EFun "v1" (EVar (Short "v2"))));
         (Short "flip",
          Closure {| sev := []; sec := [] |} "v3"
                  (EFun "v2"
                        (EFun "v1"
                              (EApp Opapp [EApp Opapp [EVar (Short "v3"); EVar (Short "v1")]; EVar (Short "v2")]))));
         (Short "id", Closure {| sev := []; sec := [] |} "v1" (EVar (Short "v1")));
         (Short "o",
          Closure {| sev := []; sec := [] |} "v2"
                  (EFun "v3"
                        (EFun "v1"
                              (EApp Opapp [EVar (Short "v2"); EApp Opapp [EVar (Short "v3"); EVar (Short "v1")]]))));
         (Short "uncurry",
          Closure
            {|
              sev := [(Short "fst",
                       Closure {| sev := []; sec := [] |} "v3"
                               (EMat (EVar (Short "v3"))
                                     [(Pcon None [Pvar "v2"; Pvar "v1"], EVar (Short "v2"))]));
                     (Short "snd",
                      Closure {| sev := []; sec := [] |} "v3"
                              (EMat (EVar (Short "v3"))
                                    [(Pcon None [Pvar "v2"; Pvar "v1"], EVar (Short "v1"))]))];
              sec := [] |} "v1"
            (EFun "v2"
                  (EApp Opapp
                        [EApp Opapp [EVar (Short "v1"); EApp Opapp [EVar (Short "fst"); EVar (Short "v2")]];
                        EApp Opapp [EVar (Short "snd"); EVar (Short "v2")]])));
         (Short "curry",
          Closure {| sev := []; sec := [] |} "v1"
                  (EFun "v2"
                        (EFun "v3"
                              (EApp Opapp [EVar (Short "v1"); ECon None [EVar (Short "v2"); EVar (Short "v3")]]))));
         (Short "snd",
          Closure {| sev := []; sec := [] |} "v3"
                  (EMat (EVar (Short "v3")) [(Pcon None [Pvar "v2"; Pvar "v1"], EVar (Short "v1"))]));
         (Short "fst",
          Closure {| sev := []; sec := [] |} "v3"
                  (EMat (EVar (Short "v3")) [(Pcon None [Pvar "v2"; Pvar "v1"], EVar (Short "v2"))]))];
  sec := [(Short "Inl", (1%nat, TypeStamp "Inl" 2)); (Short "Inr", (1%nat, TypeStamp "Inr" 2));
         (Short "Less", (0%nat, TypeStamp "Less" 1)); (Short "Equal", (0%nat, TypeStamp "Equal" 1));
         (Short "Greater", (0%nat, TypeStamp "Greater" 1));
         (Short "None", (0%nat, TypeStamp "None" 0)); (Short "Some", (1%nat, TypeStamp "Some" 0))] |}.

Definition env_27 := {|
    sev := [(Long "List" (Short "sort"),
            Recclosure
              {|
              sev := (Short "partition_1",
                     Closure
                       {|
                       sev := (Short "part",
                              Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                                [("part", "v3",
                                 EFun "v6"
                                   (EFun "v4"
                                      (EFun "v5"
                                         (EMat (EVar (Short "v6"))
                                            [(Pcon (Some (Short "[]")) [],
                                             ECon None [EVar (Short "v4"); EVar (Short "v5")]);
                                            (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                                            EIf (EApp Opapp [EVar (Short "v3"); EVar (Short "v2")])
                                              (EApp Opapp
                                                 [EApp Opapp
                                                    [EApp Opapp
                                                       [EApp Opapp
                                                          [EVar (Short "part"); EVar (Short "v3")];
                                                       EVar (Short "v1")];
                                                    ECon (Some (Short "::"))
                                                      [EVar (Short "v2"); EVar (Short "v4")]];
                                                 EVar (Short "v5")])
                                              (EApp Opapp
                                                 [EApp Opapp
                                                    [EApp Opapp
                                                       [EApp Opapp
                                                          [EVar (Short "part"); EVar (Short "v3")];
                                                       EVar (Short "v1")];
                                                    EVar (Short "v4")];
                                                 ECon (Some (Short "::"))
                                                   [EVar (Short "v2"); EVar (Short "v5")]]))]))))]
                                "part") :: nsEmpty;
                       sec := nsEmpty |} "v1"
                       (EFun "v2"
                          (EApp Opapp
                             [EApp Opapp
                                [EApp Opapp
                                   [EApp Opapp [EVar (Short "part"); EVar (Short "v1")];
                                   EVar (Short "v2")]; ECon (Some (Short "[]")) []];
                             ECon (Some (Short "[]")) []]))) :: nsEmpty;
              sec := nsEmpty |}
              [("sort", "v7",
               EFun "v8"
                 (EMat (EVar (Short "v8"))
                    [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                    (Pcon (Some (Short "::")) [Pvar "v6"; Pvar "v5"],
                    ELet (Some "v3")
                      (EApp Opapp
                         [EApp Opapp
                            [EVar (Short "partition_1");
                            EFun "v4"
                              (EApp Opapp
                                 [EApp Opapp [EVar (Short "v7"); EVar (Short "v4")]; EVar (Short "v6")])];
                         EVar (Short "v5")])
                      (EMat (EVar (Short "v3"))
                         [(Pcon None [Pvar "v2"; Pvar "v1"],
                          EApp ListAppend
                            [EApp ListAppend
                               [EApp Opapp
                                  [EApp Opapp [EVar (Short "sort"); EVar (Short "v7")];
                                  EVar (Short "v2")];
                               ECon (Some (Short "::"))
                                 [EVar (Short "v6"); ECon (Some (Short "[]")) []]];
                            EApp Opapp
                              [EApp Opapp [EVar (Short "sort"); EVar (Short "v7")]; EVar (Short "v1")]])]))]))]
              "sort");
           (Long "List" (Short "compare"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("compare", "v7",
              EFun "v8"
                (EFun "v9"
                   (EMat (EVar (Short "v8"))
                      [(Pcon (Some (Short "[]")) [],
                       EMat (EVar (Short "v9"))
                         [(Pcon (Some (Short "[]")) [], ECon (Some (Short "Equal")) []);
                         (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                         ECon (Some (Short "Less")) [])]);
                      (Pcon (Some (Short "::")) [Pvar "v6"; Pvar "v5"],
                      EMat (EVar (Short "v9"))
                        [(Pcon (Some (Short "[]")) [], ECon (Some (Short "Greater")) []);
                        (Pcon (Some (Short "::")) [Pvar "v4"; Pvar "v3"],
                        EMat
                          (EApp Opapp
                             [EApp Opapp [EVar (Short "v7"); EVar (Short "v6")]; EVar (Short "v4")])
                          [(Pcon (Some (Short "Less")) [], ECon (Some (Short "Less")) []);
                          (Pcon (Some (Short "Equal")) [],
                          EApp Opapp
                            [EApp Opapp
                               [EApp Opapp [EVar (Short "compare"); EVar (Short "v7")];
                               EVar (Short "v5")]; EVar (Short "v3")]);
                          (Pcon (Some (Short "Greater")) [], ECon (Some (Short "Greater")) [])])])])))]
             "compare");
           (Long "List" (Short "update"),
           Recclosure
             {|
             sev := (Short "update",
                    Closure {| sev := []; sec := [] |} "v3"
                      (EFun "v4"
                         (EFun "v2"
                            (EFun "v1"
                               (EIf (EApp Equality [EVar (Short "v3"); EVar (Short "v1")])
                                  (EVar (Short "v4"))
                                  (EApp Opapp [EVar (Short "v2"); EVar (Short "v1")])))))) :: nsEmpty;
             sec := nsEmpty |}
             [("update", "v8",
              EFun "v9"
                (EFun "v7"
                   (EMat (ECon None [EVar (Short "v9"); EVar (Short "v7")])
                      [(Pcon None [Pvar "v6"; Pvar "v5"],
                       EIf (EApp Equality [EVar (Short "v6"); ELit (IntLit 0)])
                         (EMat (EVar (Short "v5"))
                            [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                            (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                            ECon (Some (Short "::")) [EVar (Short "v8"); EVar (Short "v1")])])
                         (EMat (EVar (Short "v5"))
                            [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                            (Pcon (Some (Short "::")) [Pvar "v4"; Pvar "v3"],
                            ECon (Some (Short "::"))
                              [EVar (Short "v4");
                              EApp Opapp
                                [EApp Opapp
                                   [EApp Opapp [EVar (Short "update"); EVar (Short "v8")];
                                   ELet (Some "k")
                                     (EApp (Opn Minus) [EVar (Short "v6"); ELit (IntLit 1)])
                                     (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                        (ELit (IntLit 0)) (EVar (Short "k")))];
                                EVar (Short "v3")]])]))])))] "update");
           (Long "List" (Short "splitAtPki"),
           Recclosure
             {|
             sev := (Short "o",
                    Closure {| sev := []; sec := [] |} "v2"
                      (EFun "v3"
                         (EFun "v1"
                            (EApp Opapp
                               [EVar (Short "v2"); EApp Opapp [EVar (Short "v3"); EVar (Short "v1")]]))))
                    :: nsEmpty;
             sec := nsEmpty |}
             [("splitAtPki", "v6",
              EFun "v7"
                (EFun "v8"
                   (EMat (EVar (Short "v8"))
                      [(Pcon (Some (Short "[]")) [],
                       EApp Opapp
                         [EApp Opapp [EVar (Short "v7"); ECon (Some (Short "[]")) []];
                         ECon (Some (Short "[]")) []]);
                      (Pcon (Some (Short "::")) [Pvar "v5"; Pvar "v4"],
                      EIf
                        (EApp Opapp
                           [EApp Opapp [EVar (Short "v6"); ELit (IntLit 0)]; EVar (Short "v5")])
                        (EApp Opapp
                           [EApp Opapp [EVar (Short "v7"); ECon (Some (Short "[]")) []];
                           ECon (Some (Short "::")) [EVar (Short "v5"); EVar (Short "v4")]])
                        (EApp Opapp
                           [EApp Opapp
                              [EApp Opapp
                                 [EVar (Short "splitAtPki");
                                 EApp Opapp
                                   [EApp Opapp [EVar (Short "o"); EVar (Short "v6")];
                                   EFun "v1" (EApp (Opn Plus) [EVar (Short "v1"); ELit (IntLit 1)])]];
                              EFun "v3"
                                (EFun "v2"
                                   (EApp Opapp
                                      [EApp Opapp
                                         [EVar (Short "v7");
                                         ECon (Some (Short "::"))
                                           [EVar (Short "v5"); EVar (Short "v3")]];
                                      EVar (Short "v2")]))]; EVar (Short "v4")]))])))] "splitAtPki");
           (Long "List" (Short "front"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("front", "x0",
              EMat (EVar (Short "x0"))
                [(Pcon (Some (Short "[]")) [], ERaise (ECon (Some (Short "Bind")) []));
                (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                EIf (EApp Equality [EVar (Short "v1"); ECon (Some (Short "[]")) []])
                  (ECon (Some (Short "[]")) [])
                  (ECon (Some (Short "::"))
                     [EVar (Short "v2"); EApp Opapp [EVar (Short "front"); EVar (Short "v1")]]))])]
             "front");
           (Long "List" (Short "isPrefix"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("isPrefix", "v5",
              EFun "v6"
                (EMat (EVar (Short "v5"))
                   [(Pcon (Some (Short "[]")) [], EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)]);
                   (Pcon (Some (Short "::")) [Pvar "v4"; Pvar "v3"],
                   EMat (EVar (Short "v6"))
                     [(Pcon (Some (Short "[]")) [], EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]);
                     (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                     ELog And (EApp Equality [EVar (Short "v4"); EVar (Short "v2")])
                       (EApp Opapp
                          [EApp Opapp [EVar (Short "isPrefix"); EVar (Short "v3")]; EVar (Short "v1")]))])]))]
             "isPrefix");
           (Long "List" (Short "all_distinct"),
           Recclosure
             {|
             sev := (Short "member",
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("member", "v4",
                       EFun "v3"
                         (EMat (EVar (Short "v3"))
                            [(Pcon (Some (Short "[]")) [],
                             EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]);
                            (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                            ELog Or (EApp Equality [EVar (Short "v4"); EVar (Short "v2")])
                              (EApp Opapp
                                 [EApp Opapp [EVar (Short "member"); EVar (Short "v4")];
                                 EVar (Short "v1")]))]))] "member") :: nsEmpty;
             sec := nsEmpty |}
             [("all_distinct", "v3",
              EMat (EVar (Short "v3"))
                [(Pcon (Some (Short "[]")) [], EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)]);
                (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                ELog And
                  (EApp Equality
                     [EApp Opapp
                        [EApp Opapp [EVar (Short "member"); EVar (Short "v2")]; EVar (Short "v1")];
                     EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]])
                  (EApp Opapp [EVar (Short "all_distinct"); EVar (Short "v1")]))])] "all_distinct");
           (Long "List" (Short "pad_left"),
           Closure
             {|
             sev := (Short "genlist",
                    Closure
                      {|
                      sev := (Short "genlist_aux",
                             Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                               [("genlist_aux", "v1",
                                EFun "v3"
                                  (EFun "v2"
                                     (EIf (EApp Equality [EVar (Short "v3"); ELit (IntLit 0)])
                                        (EVar (Short "v2"))
                                        (EApp Opapp
                                           [EApp Opapp
                                              [EApp Opapp
                                                 [EVar (Short "genlist_aux"); EVar (Short "v1")];
                                              ELet (Some "k")
                                                (EApp (Opn Minus) [EVar (Short "v3"); ELit (IntLit 1)])
                                                (EIf
                                                   (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                                   (ELit (IntLit 0)) (EVar (Short "k")))];
                                           ECon (Some (Short "::"))
                                             [EApp Opapp
                                                [EVar (Short "v1");
                                                ELet (Some "k")
                                                  (EApp (Opn Minus)
                                                     [EVar (Short "v3"); ELit (IntLit 1)])
                                                  (EIf
                                                     (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                                     (ELit (IntLit 0)) (EVar (Short "k")))];
                                             EVar (Short "v2")]]))))] "genlist_aux") :: nsEmpty;
                      sec := nsEmpty |} "v1"
                      (EFun "v2"
                         (EApp Opapp
                            [EApp Opapp
                               [EApp Opapp [EVar (Short "genlist_aux"); EVar (Short "v1")];
                               EVar (Short "v2")]; ECon (Some (Short "[]")) []])))
                    :: (Short "const",
                       Closure {| sev := []; sec := [] |} "v2" (EFun "v1" (EVar (Short "v2"))))
                       :: (Short "length",
                          Closure
                            {|
                            sev := (Short "length_aux",
                                   Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                                     [("length_aux", "v3",
                                      EFun "v4"
                                        (EMat (EVar (Short "v3"))
                                           [(Pcon (Some (Short "[]")) [], EVar (Short "v4"));
                                           (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                                           EApp Opapp
                                             [EApp Opapp [EVar (Short "length_aux"); EVar (Short "v1")];
                                             EApp (Opn Plus) [EVar (Short "v4"); ELit (IntLit 1)]])]))]
                                     "length_aux") :: nsEmpty;
                            sec := nsEmpty |} "v1"
                            (EApp Opapp
                               [EApp Opapp [EVar (Short "length_aux"); EVar (Short "v1")];
                               ELit (IntLit 0)])) :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EFun "v2"
                (EFun "v3"
                   (EApp ListAppend
                      [EApp Opapp
                         [EApp Opapp
                            [EVar (Short "genlist");
                            EApp Opapp [EVar (Short "const"); EVar (Short "v1")]];
                         ELet (Some "k")
                           (EApp (Opn Minus)
                              [EVar (Short "v2");
                              EApp Opapp [EVar (Short "length"); EVar (Short "v3")]])
                           (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                              (ELit (IntLit 0)) (EVar (Short "k")))]; EVar (Short "v3")]))));
           (Long "List" (Short "pad_right"),
           Closure
             {|
             sev := (Short "genlist",
                    Closure
                      {|
                      sev := (Short "genlist_aux",
                             Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                               [("genlist_aux", "v1",
                                EFun "v3"
                                  (EFun "v2"
                                     (EIf (EApp Equality [EVar (Short "v3"); ELit (IntLit 0)])
                                        (EVar (Short "v2"))
                                        (EApp Opapp
                                           [EApp Opapp
                                              [EApp Opapp
                                                 [EVar (Short "genlist_aux"); EVar (Short "v1")];
                                              ELet (Some "k")
                                                (EApp (Opn Minus) [EVar (Short "v3"); ELit (IntLit 1)])
                                                (EIf
                                                   (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                                   (ELit (IntLit 0)) (EVar (Short "k")))];
                                           ECon (Some (Short "::"))
                                             [EApp Opapp
                                                [EVar (Short "v1");
                                                ELet (Some "k")
                                                  (EApp (Opn Minus)
                                                     [EVar (Short "v3"); ELit (IntLit 1)])
                                                  (EIf
                                                     (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                                     (ELit (IntLit 0)) (EVar (Short "k")))];
                                             EVar (Short "v2")]]))))] "genlist_aux") :: nsEmpty;
                      sec := nsEmpty |} "v1"
                      (EFun "v2"
                         (EApp Opapp
                            [EApp Opapp
                               [EApp Opapp [EVar (Short "genlist_aux"); EVar (Short "v1")];
                               EVar (Short "v2")]; ECon (Some (Short "[]")) []])))
                    :: (Short "const",
                       Closure {| sev := []; sec := [] |} "v2" (EFun "v1" (EVar (Short "v2"))))
                       :: (Short "length",
                          Closure
                            {|
                            sev := (Short "length_aux",
                                   Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                                     [("length_aux", "v3",
                                      EFun "v4"
                                        (EMat (EVar (Short "v3"))
                                           [(Pcon (Some (Short "[]")) [], EVar (Short "v4"));
                                           (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                                           EApp Opapp
                                             [EApp Opapp [EVar (Short "length_aux"); EVar (Short "v1")];
                                             EApp (Opn Plus) [EVar (Short "v4"); ELit (IntLit 1)]])]))]
                                     "length_aux") :: nsEmpty;
                            sec := nsEmpty |} "v1"
                            (EApp Opapp
                               [EApp Opapp [EVar (Short "length_aux"); EVar (Short "v1")];
                               ELit (IntLit 0)])) :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EFun "v2"
                (EFun "v3"
                   (EApp ListAppend
                      [EVar (Short "v3");
                      EApp Opapp
                        [EApp Opapp
                           [EVar (Short "genlist");
                           EApp Opapp [EVar (Short "const"); EVar (Short "v1")]];
                        ELet (Some "k")
                          (EApp (Opn Minus)
                             [EVar (Short "v2"); EApp Opapp [EVar (Short "length"); EVar (Short "v3")]])
                          (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                             (ELit (IntLit 0)) (EVar (Short "k")))]]))));
           (Long "List" (Short "unzip"),
           Recclosure
             {|
             sev := (Short "fst",
                    Closure {| sev := []; sec := [] |} "v3"
                      (EMat (EVar (Short "v3")) [(Pcon None [Pvar "v2"; Pvar "v1"], EVar (Short "v2"))]))
                    :: (Short "fst",
                       Closure {| sev := []; sec := [] |} "v3"
                         (EMat (EVar (Short "v3"))
                            [(Pcon None [Pvar "v2"; Pvar "v1"], EVar (Short "v2"))]))
                       :: (Short "snd",
                          Closure {| sev := []; sec := [] |} "v3"
                            (EMat (EVar (Short "v3"))
                               [(Pcon None [Pvar "v2"; Pvar "v1"], EVar (Short "v1"))]))
                          :: (Short "snd",
                             Closure {| sev := []; sec := [] |} "v3"
                               (EMat (EVar (Short "v3"))
                                  [(Pcon None [Pvar "v2"; Pvar "v1"], EVar (Short "v1"))])) :: nsEmpty;
             sec := nsEmpty |}
             [("unzip", "v3",
              EMat (EVar (Short "v3"))
                [(Pcon (Some (Short "[]")) [],
                 ECon None [ECon (Some (Short "[]")) []; ECon (Some (Short "[]")) []]);
                (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                ECon None
                  [ECon (Some (Short "::"))
                     [EApp Opapp [EVar (Short "fst"); EVar (Short "v2")];
                     EApp Opapp
                       [EVar (Short "fst"); EApp Opapp [EVar (Short "unzip"); EVar (Short "v1")]]];
                  ECon (Some (Short "::"))
                    [EApp Opapp [EVar (Short "snd"); EVar (Short "v2")];
                    EApp Opapp
                      [EVar (Short "snd"); EApp Opapp [EVar (Short "unzip"); EVar (Short "v1")]]]])])]
             "unzip");
           (Long "List" (Short "sum"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("sum", "v3",
              EMat (EVar (Short "v3"))
                [(Pcon (Some (Short "[]")) [], ELit (IntLit 0));
                (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                EApp (Opn Plus) [EVar (Short "v2"); EApp Opapp [EVar (Short "sum"); EVar (Short "v1")]])])]
             "sum");
           (Long "List" (Short "member"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("member", "v4",
              EFun "v3"
                (EMat (EVar (Short "v3"))
                   [(Pcon (Some (Short "[]")) [], EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]);
                   (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                   ELog Or (EApp Equality [EVar (Short "v4"); EVar (Short "v2")])
                     (EApp Opapp
                        [EApp Opapp [EVar (Short "member"); EVar (Short "v4")]; EVar (Short "v1")]))]))]
             "member");
           (Long "List" (Short "zip"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("zip", "v9",
              EMat (EVar (Short "v9"))
                [(Pcon None [Pvar "v8"; Pvar "v7"],
                 EMat (EVar (Short "v8"))
                   [(Pcon (Some (Short "[]")) [],
                    EMat (EVar (Short "v7"))
                      [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                      (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"], ECon (Some (Short "[]")) [])]);
                   (Pcon (Some (Short "::")) [Pvar "v6"; Pvar "v5"],
                   EMat (EVar (Short "v7"))
                     [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                     (Pcon (Some (Short "::")) [Pvar "v4"; Pvar "v3"],
                     ECon (Some (Short "::"))
                       [ECon None [EVar (Short "v6"); EVar (Short "v4")];
                       EApp Opapp
                         [EVar (Short "zip"); ECon None [EVar (Short "v5"); EVar (Short "v3")]]])])])])]
             "zip");
           (Long "List" (Short "collate"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("collate", "v7",
              EFun "v8"
                (EFun "v9"
                   (EMat (EVar (Short "v8"))
                      [(Pcon (Some (Short "[]")) [],
                       EMat (EVar (Short "v9"))
                         [(Pcon (Some (Short "[]")) [], ECon (Some (Short "Equal")) []);
                         (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                         ECon (Some (Short "Less")) [])]);
                      (Pcon (Some (Short "::")) [Pvar "v6"; Pvar "v5"],
                      EMat (EVar (Short "v9"))
                        [(Pcon (Some (Short "[]")) [], ECon (Some (Short "Greater")) []);
                        (Pcon (Some (Short "::")) [Pvar "v4"; Pvar "v3"],
                        EIf
                          (EApp Equality
                             [EApp Opapp
                                [EApp Opapp [EVar (Short "v7"); EVar (Short "v6")]; EVar (Short "v4")];
                             ECon (Some (Short "Equal")) []])
                          (EApp Opapp
                             [EApp Opapp
                                [EApp Opapp [EVar (Short "collate"); EVar (Short "v7")];
                                EVar (Short "v5")]; EVar (Short "v3")])
                          (EApp Opapp
                             [EApp Opapp [EVar (Short "v7"); EVar (Short "v6")]; EVar (Short "v4")]))])])))]
             "collate");
           (Long "List" (Short "tabulate"),
           Closure
             {|
             sev := (Short "tabulate",
                    Recclosure
                      {|
                      sev := (Short "rev",
                             Closure
                               {|
                               sev := (Short "rev",
                                      Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                                        [("rev", "v4",
                                         EFun "v3"
                                           (EMat (EVar (Short "v4"))
                                              [(Pcon (Some (Short "[]")) [], EVar (Short "v3"));
                                              (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                                              EApp Opapp
                                                [EApp Opapp [EVar (Short "rev"); EVar (Short "v1")];
                                                ECon (Some (Short "::"))
                                                  [EVar (Short "v2"); EVar (Short "v3")]])]))] "rev")
                                      :: nsEmpty;
                               sec := nsEmpty |} "v1"
                               (EApp Opapp
                                  [EApp Opapp [EVar (Short "rev"); EVar (Short "v1")];
                                  ECon (Some (Short "[]")) []])) :: nsEmpty;
                      sec := nsEmpty |}
                      [("tabulate", "v8",
                       EFun "v7"
                         (EFun "v6"
                            (EFun "v5"
                               (ELet (Some "v4")
                                  (EApp (Opb Geq) [EVar (Short "v8"); EVar (Short "v7")])
                                  (EIf (EVar (Short "v4"))
                                     (EApp Opapp [EVar (Short "rev"); EVar (Short "v5")])
                                     (ELet (Some "v3")
                                        (EApp Opapp [EVar (Short "v6"); EVar (Short "v8")])
                                        (ELet (Some "v2")
                                           (EApp (Opn Plus) [EVar (Short "v8"); ELit (IntLit 1)])
                                           (ELet (Some "v1")
                                              (ECon (Some (Short "::"))
                                                 [EVar (Short "v3"); EVar (Short "v5")])
                                              (EApp Opapp
                                                 [EApp Opapp
                                                    [EApp Opapp
                                                       [EApp Opapp
                                                          [EVar (Short "tabulate"); EVar (Short "v2")];
                                                       EVar (Short "v7")];
                                                    EVar (Short "v6")]; EVar (Short "v1")])))))))))]
                      "tabulate") :: nsEmpty;
             sec := nsEmpty |} "v3"
             (EFun "v2"
                (ELet (Some "v1") (ECon (Some (Short "[]")) [])
                   (EApp Opapp
                      [EApp Opapp
                         [EApp Opapp
                            [EApp Opapp [EVar (Short "tabulate"); ELit (IntLit 0)]; EVar (Short "v3")];
                         EVar (Short "v2")]; EVar (Short "v1")]))));
           (Long "List" (Short "tabulate"),
           Recclosure
             {|
             sev := (Short "rev",
                    Closure
                      {|
                      sev := (Short "rev",
                             Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                               [("rev", "v4",
                                EFun "v3"
                                  (EMat (EVar (Short "v4"))
                                     [(Pcon (Some (Short "[]")) [], EVar (Short "v3"));
                                     (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                                     EApp Opapp
                                       [EApp Opapp [EVar (Short "rev"); EVar (Short "v1")];
                                       ECon (Some (Short "::")) [EVar (Short "v2"); EVar (Short "v3")]])]))]
                               "rev") :: nsEmpty;
                      sec := nsEmpty |} "v1"
                      (EApp Opapp
                         [EApp Opapp [EVar (Short "rev"); EVar (Short "v1")];
                         ECon (Some (Short "[]")) []])) :: nsEmpty;
             sec := nsEmpty |}
             [("tabulate", "v8",
              EFun "v7"
                (EFun "v6"
                   (EFun "v5"
                      (ELet (Some "v4") (EApp (Opb Geq) [EVar (Short "v8"); EVar (Short "v7")])
                         (EIf (EVar (Short "v4")) (EApp Opapp [EVar (Short "rev"); EVar (Short "v5")])
                            (ELet (Some "v3") (EApp Opapp [EVar (Short "v6"); EVar (Short "v8")])
                               (ELet (Some "v2") (EApp (Opn Plus) [EVar (Short "v8"); ELit (IntLit 1)])
                                  (ELet (Some "v1")
                                     (ECon (Some (Short "::")) [EVar (Short "v3"); EVar (Short "v5")])
                                     (EApp Opapp
                                        [EApp Opapp
                                           [EApp Opapp
                                              [EApp Opapp [EVar (Short "tabulate"); EVar (Short "v2")];
                                              EVar (Short "v7")]; EVar (Short "v6")];
                                        EVar (Short "v1")])))))))))] "tabulate");
           (Long "List" (Short "genlist"),
           Closure
             {|
             sev := (Short "genlist_aux",
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("genlist_aux", "v1",
                       EFun "v3"
                         (EFun "v2"
                            (EIf (EApp Equality [EVar (Short "v3"); ELit (IntLit 0)])
                               (EVar (Short "v2"))
                               (EApp Opapp
                                  [EApp Opapp
                                     [EApp Opapp [EVar (Short "genlist_aux"); EVar (Short "v1")];
                                     ELet (Some "k")
                                       (EApp (Opn Minus) [EVar (Short "v3"); ELit (IntLit 1)])
                                       (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                          (ELit (IntLit 0)) (EVar (Short "k")))];
                                  ECon (Some (Short "::"))
                                    [EApp Opapp
                                       [EVar (Short "v1");
                                       ELet (Some "k")
                                         (EApp (Opn Minus) [EVar (Short "v3"); ELit (IntLit 1)])
                                         (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                            (ELit (IntLit 0)) (EVar (Short "k")))];
                                    EVar (Short "v2")]]))))] "genlist_aux") :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EFun "v2"
                (EApp Opapp
                   [EApp Opapp
                      [EApp Opapp [EVar (Short "genlist_aux"); EVar (Short "v1")]; EVar (Short "v2")];
                   ECon (Some (Short "[]")) []])));
           (Long "List" (Short "snoc"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("snoc", "v4",
              EFun "v3"
                (EMat (EVar (Short "v3"))
                   [(Pcon (Some (Short "[]")) [],
                    ECon (Some (Short "::")) [EVar (Short "v4"); ECon (Some (Short "[]")) []]);
                   (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                   ECon (Some (Short "::"))
                     [EVar (Short "v2");
                     EApp Opapp
                       [EApp Opapp [EVar (Short "snoc"); EVar (Short "v4")]; EVar (Short "v1")]])]))]
             "snoc");
           (Long "List" (Short "all"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("all", "v3",
              EFun "v4"
                (EMat (EVar (Short "v4"))
                   [(Pcon (Some (Short "[]")) [], EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)]);
                   (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                   ELog And (EApp Opapp [EVar (Short "v3"); EVar (Short "v2")])
                     (EApp Opapp
                        [EApp Opapp [EVar (Short "all"); EVar (Short "v3")]; EVar (Short "v1")]))]))]
             "all");
           (Long "List" (Short "exists"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("exists", "v3",
              EFun "v4"
                (EMat (EVar (Short "v4"))
                   [(Pcon (Some (Short "[]")) [], EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]);
                   (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                   ELog Or (EApp Opapp [EVar (Short "v3"); EVar (Short "v2")])
                     (EApp Opapp
                        [EApp Opapp [EVar (Short "exists"); EVar (Short "v3")]; EVar (Short "v1")]))]))]
             "exists");
           (Long "List" (Short "foldri"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("foldri", "v5",
              EFun "v4"
                (EFun "v6"
                   (EMat (EVar (Short "v6"))
                      [(Pcon (Some (Short "[]")) [], EVar (Short "v4"));
                      (Pcon (Some (Short "::")) [Pvar "v3"; Pvar "v2"],
                      EApp Opapp
                        [EApp Opapp
                           [EApp Opapp [EVar (Short "v5"); ELit (IntLit 0)]; EVar (Short "v3")];
                        EApp Opapp
                          [EApp Opapp
                             [EApp Opapp
                                [EVar (Short "foldri");
                                EFun "v1"
                                  (EApp Opapp
                                     [EVar (Short "v5");
                                     EApp (Opn Plus) [EVar (Short "v1"); ELit (IntLit 1)]])];
                             EVar (Short "v4")]; EVar (Short "v2")]])])))] "foldri");
           (Long "List" (Short "foldr"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("foldr", "v4",
              EFun "v3"
                (EFun "v5"
                   (EMat (EVar (Short "v5"))
                      [(Pcon (Some (Short "[]")) [], EVar (Short "v3"));
                      (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                      EApp Opapp
                        [EApp Opapp [EVar (Short "v4"); EVar (Short "v2")];
                        EApp Opapp
                          [EApp Opapp
                             [EApp Opapp [EVar (Short "foldr"); EVar (Short "v4")]; EVar (Short "v3")];
                          EVar (Short "v1")]])])))] "foldr");
           (Long "List" (Short "foldi"),
           Closure
             {|
             sev := (Short "foldli_aux",
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("foldli_aux", "v4",
                       EFun "v3"
                         (EFun "v5"
                            (EFun "v6"
                               (EMat (EVar (Short "v6"))
                                  [(Pcon (Some (Short "[]")) [], EVar (Short "v3"));
                                  (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                                  EApp Opapp
                                    [EApp Opapp
                                       [EApp Opapp
                                          [EApp Opapp [EVar (Short "foldli_aux"); EVar (Short "v4")];
                                          EApp Opapp
                                            [EApp Opapp
                                               [EApp Opapp [EVar (Short "v4"); EVar (Short "v5")];
                                               EVar (Short "v2")]; EVar (Short "v3")]];
                                       EApp (Opn Plus) [EVar (Short "v5"); ELit (IntLit 1)]];
                                    EVar (Short "v1")])]))))] "foldli_aux") :: nsEmpty;
             sec := nsEmpty |} "v2"
             (EFun "v1"
                (EFun "v3"
                   (EApp Opapp
                      [EApp Opapp
                         [EApp Opapp
                            [EApp Opapp [EVar (Short "foldli_aux"); EVar (Short "v2")];
                            EVar (Short "v1")]; ELit (IntLit 0)]; EVar (Short "v3")]))));
           (Long "List" (Short "foldl"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("foldl", "v4",
              EFun "v3"
                (EFun "v5"
                   (EMat (EVar (Short "v5"))
                      [(Pcon (Some (Short "[]")) [], EVar (Short "v3"));
                      (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                      EApp Opapp
                        [EApp Opapp
                           [EApp Opapp [EVar (Short "foldl"); EVar (Short "v4")];
                           EApp Opapp
                             [EApp Opapp [EVar (Short "v4"); EVar (Short "v3")]; EVar (Short "v2")]];
                        EVar (Short "v1")])])))] "foldl");
           (Long "List" (Short "partition"),
           Closure
             {|
             sev := (Short "partition_aux",
                    Recclosure
                      {|
                      sev := (Short "rev",
                             Closure
                               {|
                               sev := (Short "rev",
                                      Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                                        [("rev", "v4",
                                         EFun "v3"
                                           (EMat (EVar (Short "v4"))
                                              [(Pcon (Some (Short "[]")) [], EVar (Short "v3"));
                                              (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                                              EApp Opapp
                                                [EApp Opapp [EVar (Short "rev"); EVar (Short "v1")];
                                                ECon (Some (Short "::"))
                                                  [EVar (Short "v2"); EVar (Short "v3")]])]))] "rev")
                                      :: nsEmpty;
                               sec := nsEmpty |} "v1"
                               (EApp Opapp
                                  [EApp Opapp [EVar (Short "rev"); EVar (Short "v1")];
                                  ECon (Some (Short "[]")) []]))
                             :: (Short "rev",
                                Closure
                                  {|
                                  sev := (Short "rev",
                                         Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                                           [("rev", "v4",
                                            EFun "v3"
                                              (EMat (EVar (Short "v4"))
                                                 [(Pcon (Some (Short "[]")) [], EVar (Short "v3"));
                                                 (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                                                 EApp Opapp
                                                   [EApp Opapp [EVar (Short "rev"); EVar (Short "v1")];
                                                   ECon (Some (Short "::"))
                                                     [EVar (Short "v2"); EVar (Short "v3")]])]))] "rev")
                                         :: nsEmpty;
                                  sec := nsEmpty |} "v1"
                                  (EApp Opapp
                                     [EApp Opapp [EVar (Short "rev"); EVar (Short "v1")];
                                     ECon (Some (Short "[]")) []])) :: nsEmpty;
                      sec := nsEmpty |}
                      [("partition_aux", "v3",
                       EFun "v5"
                         (EFun "v6"
                            (EFun "v4"
                               (EMat (EVar (Short "v5"))
                                  [(Pcon (Some (Short "[]")) [],
                                   ECon None
                                     [EApp Opapp [EVar (Short "rev"); EVar (Short "v6")];
                                     EApp Opapp [EVar (Short "rev"); EVar (Short "v4")]]);
                                  (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                                  EIf (EApp Opapp [EVar (Short "v3"); EVar (Short "v2")])
                                    (EApp Opapp
                                       [EApp Opapp
                                          [EApp Opapp
                                             [EApp Opapp
                                                [EVar (Short "partition_aux"); EVar (Short "v3")];
                                             EVar (Short "v1")];
                                          ECon (Some (Short "::"))
                                            [EVar (Short "v2"); EVar (Short "v6")]];
                                       EVar (Short "v4")])
                                    (EApp Opapp
                                       [EApp Opapp
                                          [EApp Opapp
                                             [EApp Opapp
                                                [EVar (Short "partition_aux"); EVar (Short "v3")];
                                             EVar (Short "v1")]; EVar (Short "v6")];
                                       ECon (Some (Short "::")) [EVar (Short "v2"); EVar (Short "v4")]]))]))))]
                      "partition_aux") :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EFun "v2"
                (EApp Opapp
                   [EApp Opapp
                      [EApp Opapp
                         [EApp Opapp [EVar (Short "partition_aux"); EVar (Short "v1")];
                         EVar (Short "v2")]; ECon (Some (Short "[]")) []];
                   ECon (Some (Short "[]")) []])));
           (Long "List" (Short "filter"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("filter", "v3",
              EFun "v4"
                (EMat (EVar (Short "v4"))
                   [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                   EIf (EApp Opapp [EVar (Short "v3"); EVar (Short "v2")])
                     (ECon (Some (Short "::"))
                        [EVar (Short "v2");
                        EApp Opapp
                          [EApp Opapp [EVar (Short "filter"); EVar (Short "v3")]; EVar (Short "v1")]])
                     (EApp Opapp
                        [EApp Opapp [EVar (Short "filter"); EVar (Short "v3")]; EVar (Short "v1")]))]))]
             "filter");
           (Long "List" (Short "find"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("find", "v3",
              EFun "v4"
                (EMat (EVar (Short "v4"))
                   [(Pcon (Some (Short "[]")) [], ECon (Some (Short "None")) []);
                   (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                   EIf (EApp Opapp [EVar (Short "v3"); EVar (Short "v2")])
                     (ECon (Some (Short "Some")) [EVar (Short "v2")])
                     (EApp Opapp
                        [EApp Opapp [EVar (Short "find"); EVar (Short "v3")]; EVar (Short "v1")]))]))]
             "find");
           (Long "List" (Short "app"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("app", "f",
              EFun "ls"
                (EMat (EVar (Short "ls"))
                   [(Pcon (Some (Short "[]")) [], ECon None []);
                   (Pcon (Some (Short "::")) [Pvar "x"; Pvar "xs"],
                   ELet None (EApp Opapp [EVar (Short "f"); EVar (Short "x")])
                     (EApp Opapp [EApp Opapp [EVar (Short "app"); EVar (Short "f")]; EVar (Short "xs")]))]))]
             "app");
           (Long "List" (Short "mapPartial"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("mapPartial", "v4",
              EFun "v5"
                (EMat (EVar (Short "v5"))
                   [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::")) [Pvar "v3"; Pvar "v2"],
                   EMat (EApp Opapp [EVar (Short "v4"); EVar (Short "v3")])
                     [(Pcon (Some (Short "None")) [],
                      EApp Opapp
                        [EApp Opapp [EVar (Short "mapPartial"); EVar (Short "v4")]; EVar (Short "v2")]);
                     (Pcon (Some (Short "Some")) [Pvar "v1"],
                     ECon (Some (Short "::"))
                       [EVar (Short "v1");
                       EApp Opapp
                         [EApp Opapp [EVar (Short "mapPartial"); EVar (Short "v4")]; EVar (Short "v2")]])])]))]
             "mapPartial");
           (Long "List" (Short "mapi"),
           Closure
             {|
             sev := (Short "mapi",
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("mapi", "v4",
                       EFun "v5"
                         (EFun "v6"
                            (EMat (EVar (Short "v6"))
                               [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                               (Pcon (Some (Short "::")) [Pvar "v3"; Pvar "v2"],
                               ELet (Some "v1")
                                 (EApp Opapp
                                    [EApp Opapp [EVar (Short "v4"); EVar (Short "v5")];
                                    EVar (Short "v3")])
                                 (ECon (Some (Short "::"))
                                    [EVar (Short "v1");
                                    EApp Opapp
                                      [EApp Opapp
                                         [EApp Opapp [EVar (Short "mapi"); EVar (Short "v4")];
                                         EApp (Opn Plus) [EVar (Short "v5"); ELit (IntLit 1)]];
                                      EVar (Short "v2")]]))])))] "mapi") :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EFun "v2"
                (EApp Opapp
                   [EApp Opapp [EApp Opapp [EVar (Short "mapi"); EVar (Short "v1")]; ELit (IntLit 0)];
                   EVar (Short "v2")])));
           (Long "List" (Short "map"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("map", "v4",
              EFun "v5"
                (EMat (EVar (Short "v5"))
                   [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::")) [Pvar "v3"; Pvar "v2"],
                   ELet (Some "v1") (EApp Opapp [EVar (Short "v4"); EVar (Short "v3")])
                     (ECon (Some (Short "::"))
                        [EVar (Short "v1");
                        EApp Opapp
                          [EApp Opapp [EVar (Short "map"); EVar (Short "v4")]; EVar (Short "v2")]]))]))]
             "map");
           (Long "List" (Short "concat"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("concat", "v3",
              EMat (EVar (Short "v3"))
                [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                EApp ListAppend
                  [EVar (Short "v2"); EApp Opapp [EVar (Short "concat"); EVar (Short "v1")]])])]
             "concat");
           (Long "List" (Short "cmp"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("cmp", "v7",
              EFun "v8"
                (EFun "v9"
                   (EMat (EVar (Short "v8"))
                      [(Pcon (Some (Short "[]")) [],
                       EMat (EVar (Short "v9"))
                         [(Pcon (Some (Short "[]")) [], ECon (Some (Short "Equal")) []);
                         (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                         ECon (Some (Short "Less")) [])]);
                      (Pcon (Some (Short "::")) [Pvar "v6"; Pvar "v5"],
                      EMat (EVar (Short "v9"))
                        [(Pcon (Some (Short "[]")) [], ECon (Some (Short "Greater")) []);
                        (Pcon (Some (Short "::")) [Pvar "v4"; Pvar "v3"],
                        EMat
                          (EApp Opapp
                             [EApp Opapp [EVar (Short "v7"); EVar (Short "v6")]; EVar (Short "v4")])
                          [(Pcon (Some (Short "Less")) [], ECon (Some (Short "Less")) []);
                          (Pcon (Some (Short "Equal")) [],
                          EApp Opapp
                            [EApp Opapp
                               [EApp Opapp [EVar (Short "cmp"); EVar (Short "v7")]; EVar (Short "v5")];
                            EVar (Short "v3")]);
                          (Pcon (Some (Short "Greater")) [], ECon (Some (Short "Greater")) [])])])])))]
             "cmp");
           (Long "List" (Short "dropUntil"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("dropUntil", "v3",
              EFun "v4"
                (EMat (EVar (Short "v4"))
                   [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                   EIf (EApp Opapp [EVar (Short "v3"); EVar (Short "v2")])
                     (ECon (Some (Short "::")) [EVar (Short "v2"); EVar (Short "v1")])
                     (EApp Opapp
                        [EApp Opapp [EVar (Short "dropUntil"); EVar (Short "v3")]; EVar (Short "v1")]))]))]
             "dropUntil");
           (Long "List" (Short "takeUntil"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("takeUntil", "v3",
              EFun "v4"
                (EMat (EVar (Short "v4"))
                   [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                   EIf (EApp Opapp [EVar (Short "v3"); EVar (Short "v2")])
                     (ECon (Some (Short "[]")) [])
                     (ECon (Some (Short "::"))
                        [EVar (Short "v2");
                        EApp Opapp
                          [EApp Opapp [EVar (Short "takeUntil"); EVar (Short "v3")]; EVar (Short "v1")]]))]))]
             "takeUntil");
           (Long "List" (Short "drop"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("drop", "v3",
              EFun "v4"
                (EMat (EVar (Short "v3"))
                   [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                   EIf (EApp Equality [EVar (Short "v4"); ELit (IntLit 0)])
                     (ECon (Some (Short "::")) [EVar (Short "v2"); EVar (Short "v1")])
                     (EApp Opapp
                        [EApp Opapp [EVar (Short "drop"); EVar (Short "v1")];
                        ELet (Some "k") (EApp (Opn Minus) [EVar (Short "v4"); ELit (IntLit 1)])
                          (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                             (ELit (IntLit 0)) (EVar (Short "k")))]))]))] "drop");
           (Long "List" (Short "take"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("take", "v3",
              EFun "v4"
                (EMat (EVar (Short "v3"))
                   [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                   EIf (EApp Equality [EVar (Short "v4"); ELit (IntLit 0)])
                     (ECon (Some (Short "[]")) [])
                     (ECon (Some (Short "::"))
                        [EVar (Short "v2");
                        EApp Opapp
                          [EApp Opapp [EVar (Short "take"); EVar (Short "v1")];
                          ELet (Some "k") (EApp (Opn Minus) [EVar (Short "v4"); ELit (IntLit 1)])
                            (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                               (ELit (IntLit 0)) (EVar (Short "k")))]]))]))] "take");
           (Long "List" (Short "nth"),
           Recclosure
             {|
             sev := (Short "hd",
                    Closure {| sev := nsEmpty; sec := nsEmpty |} "x0"
                      (EMat (EVar (Short "x0"))
                         [(Pcon (Some (Short "[]")) [], ERaise (ECon (Some (Short "Bind")) []));
                         (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"], EVar (Short "v2"))]))
                    :: (Short "tl",
                       Closure {| sev := nsEmpty; sec := nsEmpty |} "v3"
                         (EMat (EVar (Short "v3"))
                            [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                            (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"], EVar (Short "v1"))]))
                       :: nsEmpty;
             sec := nsEmpty |}
             [("nth", "v1",
              EFun "v2"
                (EIf (EApp Equality [EVar (Short "v2"); ELit (IntLit 0)])
                   (EApp Opapp [EVar (Short "hd"); EVar (Short "v1")])
                   (EApp Opapp
                      [EApp Opapp
                         [EVar (Short "nth"); EApp Opapp [EVar (Short "tl"); EVar (Short "v1")]];
                      ELet (Some "k") (EApp (Opn Minus) [EVar (Short "v2"); ELit (IntLit 1)])
                        (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                           (ELit (IntLit 0)) (EVar (Short "k")))])))] "nth");
           (Long "List" (Short "getItem"),
           Closure
             {|
             sev := nsEmpty;
             sec := (Short "None", (0%nat, TypeStamp "None" 0))
                    :: (Short "Some", (1%nat, TypeStamp "Some" 0)) :: nsEmpty |} "v3"
             (EMat (EVar (Short "v3"))
                [(Pcon (Some (Short "[]")) [], ECon (Some (Short "None")) []);
                (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                ECon (Some (Short "Some")) [ECon None [EVar (Short "v2"); EVar (Short "v1")]])]));
           (Long "List" (Short "last"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("last", "x0",
              EMat (EVar (Short "x0"))
                [(Pcon (Some (Short "[]")) [], ERaise (ECon (Some (Short "Bind")) []));
                (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                EIf (EApp Equality [EVar (Short "v1"); ECon (Some (Short "[]")) []])
                  (EVar (Short "v2")) (EApp Opapp [EVar (Short "last"); EVar (Short "v1")]))])] "last");
           (Long "List" (Short "tl"),
           Closure {| sev := nsEmpty; sec := nsEmpty |} "v3"
             (EMat (EVar (Short "v3"))
                [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"], EVar (Short "v1"))]));
           (Long "List" (Short "hd"),
           Closure {| sev := nsEmpty; sec := nsEmpty |} "x0"
             (EMat (EVar (Short "x0"))
                [(Pcon (Some (Short "[]")) [], ERaise (ECon (Some (Short "Bind")) []));
                (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"], EVar (Short "v2"))]));
           (Long "List" (Short "@"),
           Closure {| sev := nsEmpty; sec := nsEmpty |} "v1"
             (EFun "v2" (EApp ListAppend [EVar (Short "v1"); EVar (Short "v2")])));
           (Long "List" (Short "rev"),
           Closure
             {|
             sev := (Short "rev",
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("rev", "v4",
                       EFun "v3"
                         (EMat (EVar (Short "v4"))
                            [(Pcon (Some (Short "[]")) [], EVar (Short "v3"));
                            (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                            EApp Opapp
                              [EApp Opapp [EVar (Short "rev"); EVar (Short "v1")];
                              ECon (Some (Short "::")) [EVar (Short "v2"); EVar (Short "v3")]])]))]
                      "rev") :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EApp Opapp
                [EApp Opapp [EVar (Short "rev"); EVar (Short "v1")]; ECon (Some (Short "[]")) []]));
           (Long "List" (Short "length"),
           Closure
             {|
             sev := (Short "length_aux",
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("length_aux", "v3",
                       EFun "v4"
                         (EMat (EVar (Short "v3"))
                            [(Pcon (Some (Short "[]")) [], EVar (Short "v4"));
                            (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                            EApp Opapp
                              [EApp Opapp [EVar (Short "length_aux"); EVar (Short "v1")];
                              EApp (Opn Plus) [EVar (Short "v4"); ELit (IntLit 1)]])]))] "length_aux")
                    :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EApp Opapp [EApp Opapp [EVar (Short "length_aux"); EVar (Short "v1")]; ELit (IntLit 0)]));
           (Long "List" (Short "null"),
           Closure {| sev := nsEmpty; sec := nsEmpty |} "v3"
             (EMat (EVar (Short "v3"))
                [(Pcon (Some (Short "[]")) [], EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)]);
                (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)])]));
           (Long "Option" (Short "compare"),
           Closure
             {|
             sev := [];
             sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Equal", (0%nat, TypeStamp "Equal" 1));
                    (Short "Some", (1%nat, TypeStamp "Some" 0));
                    (Short "Less", (0%nat, TypeStamp "Less" 1));
                    (Short "Some", (1%nat, TypeStamp "Some" 0));
                    (Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Greater", (0%nat, TypeStamp "Greater" 1));
                    (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v4"
             (EFun "v5"
                (EFun "v6"
                   (EMat (EVar (Short "v5"))
                      [(Pcon (Some (Short "None")) [],
                       EMat (EVar (Short "v6"))
                         [(Pcon (Some (Short "None")) [], ECon (Some (Short "Equal")) []);
                         (Pcon (Some (Short "Some")) [Pvar "v1"], ECon (Some (Short "Less")) [])]);
                      (Pcon (Some (Short "Some")) [Pvar "v3"],
                      EMat (EVar (Short "v6"))
                        [(Pcon (Some (Short "None")) [], ECon (Some (Short "Greater")) []);
                        (Pcon (Some (Short "Some")) [Pvar "v2"],
                        EApp Opapp
                          [EApp Opapp [EVar (Short "v4"); EVar (Short "v3")]; EVar (Short "v2")])])]))));
           (Long "Option" (Short "map2"),
           Closure
             {|
             sev := [(Short "isSome",
                     Closure
                       {|
                       sev := [];
                       sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                              (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v2"
                       (EMat (EVar (Short "v2"))
                          [(Pcon (Some (Short "None")) [],
                           EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]);
                          (Pcon (Some (Short "Some")) [Pvar "v1"],
                          EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)])]));
                    (Short "isSome",
                    Closure
                      {|
                      sev := [];
                      sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                             (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v2"
                      (EMat (EVar (Short "v2"))
                         [(Pcon (Some (Short "None")) [],
                          EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]);
                         (Pcon (Some (Short "Some")) [Pvar "v1"],
                         EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)])]));
                    (Short "valOf",
                    Closure
                      {|
                      sev := [];
                      sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                             (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "x0"
                      (EMat (EVar (Short "x0"))
                         [(Pcon (Some (Short "None")) [], ERaise (ECon (Some (Short "Bind")) []));
                         (Pcon (Some (Short "Some")) [Pvar "v1"], EVar (Short "v1"))]));
                    (Short "valOf",
                    Closure
                      {|
                      sev := [];
                      sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                             (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "x0"
                      (EMat (EVar (Short "x0"))
                         [(Pcon (Some (Short "None")) [], ERaise (ECon (Some (Short "Bind")) []));
                         (Pcon (Some (Short "Some")) [Pvar "v1"], EVar (Short "v1"))]))];
             sec := [(Short "Some", (1%nat, TypeStamp "Some" 0));
                    (Short "None", (0%nat, TypeStamp "None" 0))] |} "v1"
             (EFun "v2"
                (EFun "v3"
                   (EIf
                      (ELog And (EApp Opapp [EVar (Short "isSome"); EVar (Short "v2")])
                         (EApp Opapp [EVar (Short "isSome"); EVar (Short "v3")]))
                      (ECon (Some (Short "Some"))
                         [EApp Opapp
                            [EApp Opapp
                               [EVar (Short "v1");
                               EApp Opapp [EVar (Short "valOf"); EVar (Short "v2")]];
                            EApp Opapp [EVar (Short "valOf"); EVar (Short "v3")]]])
                      (ECon (Some (Short "None")) [])))));
           (Long "Option" (Short "isNone"),
           Closure
             {|
             sev := [];
             sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v2"
             (EMat (EVar (Short "v2"))
                [(Pcon (Some (Short "None")) [], EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)]);
                (Pcon (Some (Short "Some")) [Pvar "v1"],
                EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)])]));
           (Long "Option" (Short "composePartial"),
           Closure
             {|
             sev := [];
             sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v3"
             (EFun "v4"
                (EFun "v2"
                   (EMat (EApp Opapp [EVar (Short "v4"); EVar (Short "v2")])
                      [(Pcon (Some (Short "None")) [], ECon (Some (Short "None")) []);
                      (Pcon (Some (Short "Some")) [Pvar "v1"],
                      EApp Opapp [EVar (Short "v3"); EVar (Short "v1")])]))));
           (Long "Option" (Short "compose"),
           Closure
             {|
             sev := [];
             sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v3"
             (EFun "v4"
                (EFun "v2"
                   (EMat (EApp Opapp [EVar (Short "v4"); EVar (Short "v2")])
                      [(Pcon (Some (Short "None")) [], ECon (Some (Short "None")) []);
                      (Pcon (Some (Short "Some")) [Pvar "v1"],
                      ECon (Some (Short "Some")) [EApp Opapp [EVar (Short "v3"); EVar (Short "v1")]])]))));
           (Long "Option" (Short "mapPartial"),
           Closure
             {|
             sev := [];
             sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v2"
             (EFun "v3"
                (EMat (EVar (Short "v3"))
                   [(Pcon (Some (Short "None")) [], ECon (Some (Short "None")) []);
                   (Pcon (Some (Short "Some")) [Pvar "v1"],
                   EApp Opapp [EVar (Short "v2"); EVar (Short "v1")])])));
           (Long "Option" (Short "map"),
           Closure
             {|
             sev := [];
             sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v2"
             (EFun "v3"
                (EMat (EVar (Short "v3"))
                   [(Pcon (Some (Short "None")) [], ECon (Some (Short "None")) []);
                   (Pcon (Some (Short "Some")) [Pvar "v1"],
                   ECon (Some (Short "Some")) [EApp Opapp [EVar (Short "v2"); EVar (Short "v1")]])])));
           (Long "Option" (Short "join"),
           Closure
             {|
             sev := [];
             sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v2"
             (EMat (EVar (Short "v2"))
                [(Pcon (Some (Short "None")) [], ECon (Some (Short "None")) []);
                (Pcon (Some (Short "Some")) [Pvar "v1"], EVar (Short "v1"))]));
           (Long "Option" (Short "valOf"),
           Closure
             {|
             sev := [];
             sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "x0"
             (EMat (EVar (Short "x0"))
                [(Pcon (Some (Short "None")) [], ERaise (ECon (Some (Short "Bind")) []));
                (Pcon (Some (Short "Some")) [Pvar "v1"], EVar (Short "v1"))]));
           (Long "Option" (Short "isSome"),
           Closure
             {|
             sev := [];
             sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v2"
             (EMat (EVar (Short "v2"))
                [(Pcon (Some (Short "None")) [], EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]);
                (Pcon (Some (Short "Some")) [Pvar "v1"],
                EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)])]));
           (Long "Option" (Short "getOpt"),
           Closure
             {|
             sev := [];
             sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v3"
             (EFun "v2"
                (EMat (EVar (Short "v3"))
                   [(Pcon (Some (Short "None")) [], EVar (Short "v2"));
                   (Pcon (Some (Short "Some")) [Pvar "v1"], EVar (Short "v1"))])));
           (Long "Runtime" (Short "abort"),
           Recclosure
             {|
             sev := [(Short "exit",
                     Recclosure {| sev := []; sec := [] |}
                       [("exit", "i",
                        ELet (Some "y") (EApp (WordFromInt W8) [EVar (Short "i")])
                          (ELet (Some "x") (EApp Aw8alloc [ELit (IntLit 1); EVar (Short "y")])
                             (EApp (FFI "exit") [ELit (StrLit ""); EVar (Short "x")])))] "exit")];
             sec := [] |}
             [("abort", "u",
              EMat (EVar (Short "u"))
                [(Pcon None [], EApp Opapp [EVar (Short "exit"); ELit (IntLit 1)])])] "abort");
           (Long "Runtime" (Short "exit"),
           Recclosure {| sev := []; sec := [] |}
             [("exit", "i",
              ELet (Some "y") (EApp (WordFromInt W8) [EVar (Short "i")])
                (ELet (Some "x") (EApp Aw8alloc [ELit (IntLit 1); EVar (Short "y")])
                   (EApp (FFI "exit") [ELit (StrLit ""); EVar (Short "x")])))] "exit");
           (Long "Runtime" (Short "debugMsg"),
           Closure {| sev := []; sec := [] |} "v1"
             (EApp (FFI "")
                [EVar (Short "v1"); EApp Aw8alloc [ELit (IntLit 0); ELit (Word8Lit (nat_to_word 8 0))]]));
           (Long "Runtime" (Short "fail"),
           Closure {| sev := []; sec := [] |} "v1"
             (EMat (EVar (Short "v1"))
                [(Pcon None [],
                 ELet (Some "a") (EVar (Short "v1"))
                   (ELet (Some "n") (ELit (StrLit "18446744073709551616"))
                      (ELet None (EApp Aalloc [EVar (Short "n"); EVar (Short "n")]) (EVar (Short "a")))))]));
           (Long "Runtime" (Short "fullGC"),
           Closure {| sev := []; sec := [] |} "v1"
             (EMat (EVar (Short "v1"))
                [(Pcon None [], EApp ConfigGC [ELit (IntLit 0); ELit (IntLit 0)])]));
           (Short "repeat",
           Recclosure {| sev := []; sec := [] |}
             [("repeat", "f",
              EFun "x"
                (ELet (Some "a") (EApp Opapp [EVar (Short "f"); EVar (Short "x")])
                   (EApp Opapp [EApp Opapp [EVar (Short "repeat"); EVar (Short "f")]; EVar (Short "a")])))]
             "repeat");
           (Short "least",
           Closure
             {|
             sev := [(Short "while",
                     Recclosure {| sev := []; sec := [] |}
                       [("while", "v1",
                        EFun "v2"
                          (EFun "v3"
                             (EIf (EApp Opapp [EVar (Short "v1"); EVar (Short "v3")])
                                (EApp Opapp
                                   [EApp Opapp
                                      [EApp Opapp [EVar (Short "while"); EVar (Short "v1")];
                                      EVar (Short "v2")];
                                   EApp Opapp [EVar (Short "v2"); EVar (Short "v3")]])
                                (EVar (Short "v3")))))] "while")];
             sec := [] |} "v3"
             (EApp Opapp
                [EApp Opapp
                   [EApp Opapp
                      [EVar (Short "while");
                      EFun "v1"
                        (EApp Equality
                           [EApp Opapp [EVar (Short "v3"); EVar (Short "v1")];
                           EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]])];
                   EFun "v2" (EApp (Opn Plus) [EVar (Short "v2"); ELit (IntLit 1)])];
                ELit (IntLit 0)]));
           (Short "owhile",
           Recclosure {| sev := []; sec := [] |}
             [("owhile", "v1",
              EFun "v2"
                (EFun "v3"
                   (EIf (EApp Opapp [EVar (Short "v1"); EVar (Short "v3")])
                      (EApp Opapp
                         [EApp Opapp
                            [EApp Opapp [EVar (Short "owhile"); EVar (Short "v1")]; EVar (Short "v2")];
                         EApp Opapp [EVar (Short "v2"); EVar (Short "v3")]])
                      (ECon (Some (Short "Some")) [EVar (Short "v3")]))))] "owhile");
           (Short "while",
           Recclosure {| sev := []; sec := [] |}
             [("while", "v1",
              EFun "v2"
                (EFun "v3"
                   (EIf (EApp Opapp [EVar (Short "v1"); EVar (Short "v3")])
                      (EApp Opapp
                         [EApp Opapp
                            [EApp Opapp [EVar (Short "while"); EVar (Short "v1")]; EVar (Short "v2")];
                         EApp Opapp [EVar (Short "v2"); EVar (Short "v3")]])
                      (EVar (Short "v3")))))] "while");
           (Short "pre",
           Closure {| sev := []; sec := [] |} "v1"
             (ELet (Some "k") (EApp (Opn Minus) [EVar (Short "v1"); ELit (IntLit 1)])
                (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)]) (ELit (IntLit 0))
                   (EVar (Short "k")))));
           (Short "abs_diff",
           Closure {| sev := []; sec := [] |} "v2"
             (EFun "v1"
                (EIf (EApp (Opb Lt) [EVar (Short "v2"); EVar (Short "v1")])
                   (ELet (Some "k") (EApp (Opn Minus) [EVar (Short "v1"); EVar (Short "v2")])
                      (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                         (ELit (IntLit 0)) (EVar (Short "k"))))
                   (ELet (Some "k") (EApp (Opn Minus) [EVar (Short "v2"); EVar (Short "v1")])
                      (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                         (ELit (IntLit 0)) (EVar (Short "k")))))));
           (Short "funpow",
           Recclosure {| sev := []; sec := [] |}
             [("funpow", "v1",
              EFun "v2"
                (EFun "v3"
                   (EIf (EApp Equality [EVar (Short "v2"); ELit (IntLit 0)])
                      (EVar (Short "v3"))
                      (EApp Opapp
                         [EApp Opapp
                            [EApp Opapp [EVar (Short "funpow"); EVar (Short "v1")];
                            ELet (Some "k") (EApp (Opn Minus) [EVar (Short "v2"); ELit (IntLit 1)])
                              (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                 (ELit (IntLit 0)) (EVar (Short "k")))];
                         EApp Opapp [EVar (Short "v1"); EVar (Short "v3")]]))))] "funpow");
           (Short "odd",
           Closure {| sev := []; sec := [] |} "v1"
             (EApp (Opb Lt) [ELit (IntLit 0); EApp (Opn Modulo) [EVar (Short "v1"); ELit (IntLit 2)]]));
           (Short "even",
           Closure {| sev := []; sec := [] |} "v1"
             (EApp Equality [EApp (Opn Modulo) [EVar (Short "v1"); ELit (IntLit 2)]; ELit (IntLit 0)]));
           (Short "max",
           Closure {| sev := []; sec := [] |} "v1"
             (EFun "v2"
                (EIf (EApp (Opb Lt) [EVar (Short "v1"); EVar (Short "v2")])
                   (EVar (Short "v2")) (EVar (Short "v1")))));
           (Short "min",
           Closure {| sev := []; sec := [] |} "v1"
             (EFun "v2"
                (EIf (EApp (Opb Lt) [EVar (Short "v1"); EVar (Short "v2")])
                   (EVar (Short "v1")) (EVar (Short "v2")))));
           (Short "exp",
           Closure
             {|
             sev := [(Short "exp",
                     Recclosure {| sev := []; sec := [] |}
                       [("exp", "v2",
                        EFun "v3"
                          (EFun "v1"
                             (EIf (EApp Equality [EVar (Short "v3"); ELit (IntLit 0)])
                                (EVar (Short "v1"))
                                (EApp Opapp
                                   [EApp Opapp
                                      [EApp Opapp [EVar (Short "exp"); EVar (Short "v2")];
                                      ELet (Some "k")
                                        (EApp (Opn Minus) [EVar (Short "v3"); ELit (IntLit 1)])
                                        (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                           (ELit (IntLit 0)) (EVar (Short "k")))];
                                   EApp (Opn Times) [EVar (Short "v2"); EVar (Short "v1")]]))))] "exp")];
             sec := [] |} "v1"
             (EFun "v2"
                (EApp Opapp
                   [EApp Opapp [EApp Opapp [EVar (Short "exp"); EVar (Short "v1")]; EVar (Short "v2")];
                   ELit (IntLit 1)])));
           (Short "exp",
           Recclosure {| sev := []; sec := [] |}
             [("exp", "v2",
              EFun "v3"
                (EFun "v1"
                   (EIf (EApp Equality [EVar (Short "v3"); ELit (IntLit 0)])
                      (EVar (Short "v1"))
                      (EApp Opapp
                         [EApp Opapp
                            [EApp Opapp [EVar (Short "exp"); EVar (Short "v2")];
                            ELet (Some "k") (EApp (Opn Minus) [EVar (Short "v3"); ELit (IntLit 1)])
                              (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                 (ELit (IntLit 0)) (EVar (Short "k")))];
                         EApp (Opn Times) [EVar (Short "v2"); EVar (Short "v1")]]))))] "exp");
           (Short "update",
           Closure {| sev := []; sec := [] |} "v3"
             (EFun "v4"
                (EFun "v2"
                   (EFun "v1"
                      (EIf (EApp Equality [EVar (Short "v3"); EVar (Short "v1")])
                         (EVar (Short "v4")) (EApp Opapp [EVar (Short "v2"); EVar (Short "v1")]))))));
           (Short "const", Closure {| sev := []; sec := [] |} "v2" (EFun "v1" (EVar (Short "v2"))));
           (Short "flip",
           Closure {| sev := []; sec := [] |} "v3"
             (EFun "v2"
                (EFun "v1"
                   (EApp Opapp [EApp Opapp [EVar (Short "v3"); EVar (Short "v1")]; EVar (Short "v2")]))));
           (Short "id", Closure {| sev := []; sec := [] |} "v1" (EVar (Short "v1")));
           (Short "o",
           Closure {| sev := []; sec := [] |} "v2"
             (EFun "v3"
                (EFun "v1"
                   (EApp Opapp [EVar (Short "v2"); EApp Opapp [EVar (Short "v3"); EVar (Short "v1")]]))));
           (Short "uncurry",
           Closure
             {|
             sev := [(Short "fst",
                     Closure {| sev := []; sec := [] |} "v3"
                       (EMat (EVar (Short "v3"))
                          [(Pcon None [Pvar "v2"; Pvar "v1"], EVar (Short "v2"))]));
                    (Short "snd",
                    Closure {| sev := []; sec := [] |} "v3"
                      (EMat (EVar (Short "v3")) [(Pcon None [Pvar "v2"; Pvar "v1"], EVar (Short "v1"))]))];
             sec := [] |} "v1"
             (EFun "v2"
                (EApp Opapp
                   [EApp Opapp [EVar (Short "v1"); EApp Opapp [EVar (Short "fst"); EVar (Short "v2")]];
                   EApp Opapp [EVar (Short "snd"); EVar (Short "v2")]])));
           (Short "curry",
           Closure {| sev := []; sec := [] |} "v1"
             (EFun "v2"
                (EFun "v3"
                   (EApp Opapp [EVar (Short "v1"); ECon None [EVar (Short "v2"); EVar (Short "v3")]]))));
           (Short "snd",
           Closure {| sev := []; sec := [] |} "v3"
             (EMat (EVar (Short "v3")) [(Pcon None [Pvar "v2"; Pvar "v1"], EVar (Short "v1"))]));
           (Short "fst",
           Closure {| sev := []; sec := [] |} "v3"
             (EMat (EVar (Short "v3")) [(Pcon None [Pvar "v2"; Pvar "v1"], EVar (Short "v2"))]))];
    sec := [(Short "Inl", (1%nat, TypeStamp "Inl" 2)); (Short "Inr", (1%nat, TypeStamp "Inr" 2));
           (Short "Less", (0%nat, TypeStamp "Less" 1)); (Short "Equal", (0%nat, TypeStamp "Equal" 1));
           (Short "Greater", (0%nat, TypeStamp "Greater" 1));
           (Short "None", (0%nat, TypeStamp "None" 0)); (Short "Some", (1%nat, TypeStamp "Some" 0))] |}.

Definition env_28 := {|
    sev := [(Long "Alist" (Short "delete"),
            Recclosure
              {|
              sev := nsEmpty;
              sec := nsEmpty |}
              [("delete", "v5",
               EFun "v6"
                 (EMat (EVar (Short "v5"))
                    [(Pcon (Some (Short "[]")) [],
                     ECon (Some (Short "[]")) []);
                    (Pcon (Some (Short "::"))
                       [Pvar "v4"; Pvar "v3"],
                    EMat (EVar (Short "v4"))
                      [(Pcon None
                          [Pvar "v2"; Pvar "v1"],
                       EIf
                         (EApp Equality
                            [EVar (Short "v2");
                            EVar (Short "v6")])
                         (EApp Opapp
                            [EApp Opapp
                               [EVar
                                (Short "delete");
                               EVar (Short "v3")];
                            EVar (Short "v6")])
                         (ECon
                            (Some (Short "::"))
                            [ECon None
                               [EVar (Short "v2");
                               EVar (Short "v1")];
                            EApp Opapp
                              [EApp Opapp
                                [
                                EVar
                                (Short "delete");
                                EVar (Short "v3")];
                              EVar (Short "v6")]]))])]))]
              "delete");
           (Long "Alist" (Short "map"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("map", "v5",
              EFun "v6"
                (EMat (EVar (Short "v6"))
                   [(Pcon (Some (Short "[]")) [],
                    ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::"))
                      [Pvar "v4"; Pvar "v3"],
                   EMat (EVar (Short "v4"))
                     [(Pcon None
                         [Pvar "v2"; Pvar "v1"],
                      ECon (Some (Short "::"))
                        [ECon None
                           [EVar (Short "v2");
                           EApp Opapp
                             [EVar (Short "v5");
                             EVar (Short "v1")]];
                        EApp Opapp
                          [EApp Opapp
                             [EVar (Short "map");
                             EVar (Short "v5")];
                          EVar (Short "v3")]])])]))]
             "map");
           (Long "Alist" (Short "every"),
           Closure
             {|
             sev := (Short "every",
                    Recclosure
                      {|
                      sev := (Long "List"
                                (Short "member"),
                             Recclosure
                               {|
                               sev := nsEmpty;
                               sec := nsEmpty |}
                               [("member", "v4",
                                EFun "v3"
                                (EMat
                                (EVar
                                (Short "v3"))
                                [
                                (
                                Pcon
                                (Some
                                (Short "[]")) [],
                                EApp
                                (Opb Lt)
                                [
                                ELit (IntLit 0);
                                ELit (IntLit 0)]);
                                (
                                Pcon
                                (Some
                                (Short "::"))
                                [
                                Pvar "v2";
                                Pvar "v1"],
                                ELog Or
                                (EApp Equality
                                [
                                EVar
                                (Short "v4");
                                EVar (Short "v2")])
                                (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "member");
                                EVar (Short "v4")];
                                EVar (Short "v1")]))]))]
                               "member")
                             :: nsEmpty;
                      sec := nsEmpty |}
                      [("every", "v5",
                       EFun "v6"
                         (EFun "v7"
                            (EMat
                               (EVar (Short "v7"))
                               [(
                                Pcon
                                (Some
                                (Short "[]")) [],
                                EApp
                                (Opb Leq)
                                [
                                ELit (IntLit 0);
                                ELit (IntLit 0)]);
                               (Pcon
                                (Some
                                (Short "::"))
                                [
                                Pvar "v4";
                                Pvar "v3"],
                               EMat
                                (EVar
                                (Short "v4"))
                                [(
                                Pcon None
                                [
                                Pvar "v2";
                                Pvar "v1"],
                                EIf
                                (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Long "List"
                                (Short "member"));
                                EVar (Short "v2")];
                                EVar (Short "v5")])
                                (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "every");
                                EVar (Short "v5")];
                                EVar (Short "v6")];
                                EVar (Short "v3")])
                                (ELog And
                                (EApp Opapp
                                [
                                EVar
                                (Short "v6");
                                ECon None
                                [
                                EVar
                                (Short "v2");
                                EVar (Short "v1")]])
                                (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "every");
                                ECon
                                (Some
                                (Short "::"))
                                [
                                EVar
                                (Short "v2");
                                EVar (Short "v5")]];
                                EVar (Short "v6")];
                                EVar (Short "v3")])))])])))]
                      "every") :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EApp Opapp
                [EApp Opapp
                   [EVar (Short "every");
                   ECon (Some (Short "[]")) []];
                EVar (Short "v1")]));
           (Long "Alist" (Short "every"),
           Recclosure
             {|
             sev := (Long "List" (Short "member"),
                    Recclosure
                      {|
                      sev := nsEmpty;
                      sec := nsEmpty |}
                      [("member", "v4",
                       EFun "v3"
                         (EMat
                            (EVar (Short "v3"))
                            [(Pcon
                                (Some
                                (Short "[]")) [],
                             EApp
                               (Opb Lt)
                               [ELit (IntLit 0);
                               ELit (IntLit 0)]);
                            (Pcon
                               (Some (Short "::"))
                               [Pvar "v2";
                               Pvar "v1"],
                            ELog Or
                              (EApp Equality
                                [
                                EVar
                                (Short "v4");
                                EVar (Short "v2")])
                              (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "member");
                                EVar (Short "v4")];
                                EVar (Short "v1")]))]))]
                      "member") :: nsEmpty;
             sec := nsEmpty |}
             [("every", "v5",
              EFun "v6"
                (EFun "v7"
                   (EMat (EVar (Short "v7"))
                      [(Pcon (Some (Short "[]"))
                          [],
                       EApp (Opb Leq)
                         [ELit (IntLit 0);
                         ELit (IntLit 0)]);
                      (Pcon (Some (Short "::"))
                         [Pvar "v4"; Pvar "v3"],
                      EMat (EVar (Short "v4"))
                        [(Pcon None
                            [Pvar "v2";
                            Pvar "v1"],
                         EIf
                           (EApp Opapp
                              [EApp Opapp
                                [
                                EVar
                                (Long "List"
                                (Short "member"));
                                EVar (Short "v2")];
                              EVar (Short "v5")])
                           (EApp Opapp
                              [EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "every");
                                EVar (Short "v5")];
                                EVar (Short "v6")];
                              EVar (Short "v3")])
                           (ELog And
                              (EApp Opapp
                                [
                                EVar
                                (Short "v6");
                                ECon None
                                [
                                EVar
                                (Short "v2");
                                EVar (Short "v1")]])
                              (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "every");
                                ECon
                                (Some
                                (Short "::"))
                                [
                                EVar
                                (Short "v2");
                                EVar (Short "v5")]];
                                EVar (Short "v6")];
                                EVar (Short "v3")])))])])))]
             "every");
           (Long "Alist" (Short "update"),
           Closure
             {| sev := nsEmpty; sec := nsEmpty |}
             "v3"
             (EFun "v4"
                (EMat (EVar (Short "v4"))
                   [(Pcon None
                       [Pvar "v2"; Pvar "v1"],
                    ECon (Some (Short "::"))
                      [ECon None
                         [EVar (Short "v2");
                         EVar (Short "v1")];
                      EVar (Short "v3")])])));
           (Long "Alist" (Short "lookup"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("lookup", "v5",
              EFun "v6"
                (EMat (EVar (Short "v5"))
                   [(Pcon (Some (Short "[]")) [],
                    ECon (Some (Short "None")) []);
                   (Pcon (Some (Short "::"))
                      [Pvar "v4"; Pvar "v3"],
                   EMat (EVar (Short "v4"))
                     [(Pcon None
                         [Pvar "v2"; Pvar "v1"],
                      EIf
                        (EApp Equality
                           [EVar (Short "v2");
                           EVar (Short "v6")])
                        (ECon
                           (Some (Short "Some"))
                           [EVar (Short "v1")])
                        (EApp Opapp
                           [EApp Opapp
                              [EVar
                                (Short "lookup");
                              EVar (Short "v3")];
                           EVar (Short "v6")]))])]))]
             "lookup");
           (Long "List" (Short "sort"),
           Recclosure
             {|
             sev := (Short "partition_1",
                    Closure
                      {|
                      sev := (Short "part",
                             Recclosure
                               {|
                               sev := nsEmpty;
                               sec := nsEmpty |}
                               [("part", "v3",
                                EFun "v6"
                                (EFun "v4"
                                (EFun "v5"
                                (EMat
                                (EVar
                                (Short "v6"))
                                [
                                (
                                Pcon
                                (Some
                                (Short "[]")) [],
                                ECon None
                                [
                                EVar
                                (Short "v4");
                                EVar (Short "v5")]);
                                (
                                Pcon
                                (Some
                                (Short "::"))
                                [
                                Pvar "v2";
                                Pvar "v1"],
                                EIf
                                (EApp Opapp
                                [
                                EVar
                                (Short "v3");
                                EVar (Short "v2")])
                                (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "part");
                                EVar (Short "v3")];
                                EVar (Short "v1")];
                                ECon
                                (Some
                                (Short "::"))
                                [
                                EVar
                                (Short "v2");
                                EVar (Short "v4")]];
                                EVar (Short "v5")])
                                (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "part");
                                EVar (Short "v3")];
                                EVar (Short "v1")];
                                EVar (Short "v4")];
                                ECon
                                (Some
                                (Short "::"))
                                [
                                EVar
                                (Short "v2");
                                EVar (Short "v5")]]))]))))]
                               "part") :: nsEmpty;
                      sec := nsEmpty |} "v1"
                      (EFun "v2"
                         (EApp Opapp
                            [EApp Opapp
                               [EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "part");
                                EVar (Short "v1")];
                                EVar (Short "v2")];
                               ECon
                                (Some
                                (Short "[]")) []];
                            ECon
                              (Some (Short "[]"))
                              []]))) :: nsEmpty;
             sec := nsEmpty |}
             [("sort", "v7",
              EFun "v8"
                (EMat (EVar (Short "v8"))
                   [(Pcon (Some (Short "[]")) [],
                    ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::"))
                      [Pvar "v6"; Pvar "v5"],
                   ELet (Some "v3")
                     (EApp Opapp
                        [EApp Opapp
                           [EVar
                              (Short
                                "partition_1");
                           EFun "v4"
                             (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "v7");
                                EVar (Short "v4")];
                                EVar (Short "v6")])];
                        EVar (Short "v5")])
                     (EMat (EVar (Short "v3"))
                        [(Pcon None
                            [Pvar "v2";
                            Pvar "v1"],
                         EApp ListAppend
                           [EApp ListAppend
                              [EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "sort");
                                EVar (Short "v7")];
                                EVar (Short "v2")];
                              ECon
                                (Some
                                (Short "::"))
                                [
                                EVar
                                (Short "v6");
                                ECon
                                (Some
                                (Short "[]")) []]];
                           EApp Opapp
                             [EApp Opapp
                                [
                                EVar
                                (Short "sort");
                                EVar (Short "v7")];
                             EVar (Short "v1")]])]))]))]
             "sort");
           (Long "List" (Short "compare"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("compare", "v7",
              EFun "v8"
                (EFun "v9"
                   (EMat (EVar (Short "v8"))
                      [(Pcon (Some (Short "[]"))
                          [],
                       EMat (EVar (Short "v9"))
                         [(Pcon
                             (Some (Short "[]"))
                             [],
                          ECon
                            (Some (Short "Equal"))
                            []);
                         (Pcon
                            (Some (Short "::"))
                            [Pvar "v2";
                            Pvar "v1"],
                         ECon
                           (Some (Short "Less"))
                           [])]);
                      (Pcon (Some (Short "::"))
                         [Pvar "v6"; Pvar "v5"],
                      EMat (EVar (Short "v9"))
                        [(Pcon
                            (Some (Short "[]"))
                            [],
                         ECon
                           (Some
                              (Short "Greater"))
                           []);
                        (Pcon (Some (Short "::"))
                           [Pvar "v4"; Pvar "v3"],
                        EMat
                          (EApp Opapp
                             [EApp Opapp
                                [
                                EVar
                                (Short "v7");
                                EVar (Short "v6")];
                             EVar (Short "v4")])
                          [(Pcon
                              (Some
                                (Short "Less"))
                              [],
                           ECon
                             (Some (Short "Less"))
                             []);
                          (Pcon
                             (Some
                                (Short "Equal"))
                             [],
                          EApp Opapp
                            [EApp Opapp
                               [EApp Opapp
                                [
                                EVar
                                (Short "compare");
                                EVar (Short "v7")];
                               EVar (Short "v5")];
                            EVar (Short "v3")]);
                          (Pcon
                             (Some
                                (Short "Greater"))
                             [],
                          ECon
                            (Some
                               (Short "Greater"))
                            [])])])])))]
             "compare");
           (Long "List" (Short "update"),
           Recclosure
             {|
             sev := (Short "update",
                    Closure
                      {| sev := []; sec := [] |}
                      "v3"
                      (EFun "v4"
                         (EFun "v2"
                            (EFun "v1"
                               (EIf
                                (EApp Equality
                                [
                                EVar
                                (Short "v3");
                                EVar (Short "v1")])
                                (EVar
                                (Short "v4"))
                                (EApp Opapp
                                [
                                EVar
                                (Short "v2");
                                EVar (Short "v1")]))))))
                    :: nsEmpty;
             sec := nsEmpty |}
             [("update", "v8",
              EFun "v9"
                (EFun "v7"
                   (EMat
                      (ECon None
                         [EVar (Short "v9");
                         EVar (Short "v7")])
                      [(Pcon None
                          [Pvar "v6"; Pvar "v5"],
                       EIf
                         (EApp Equality
                            [EVar (Short "v6");
                            ELit (IntLit 0)])
                         (EMat
                            (EVar (Short "v5"))
                            [(Pcon
                                (Some
                                (Short "[]")) [],
                             ECon
                               (Some (Short "[]"))
                               []);
                            (Pcon
                               (Some (Short "::"))
                               [Pvar "v2";
                               Pvar "v1"],
                            ECon
                              (Some (Short "::"))
                              [EVar (Short "v8");
                              EVar (Short "v1")])])
                         (EMat
                            (EVar (Short "v5"))
                            [(Pcon
                                (Some
                                (Short "[]")) [],
                             ECon
                               (Some (Short "[]"))
                               []);
                            (Pcon
                               (Some (Short "::"))
                               [Pvar "v4";
                               Pvar "v3"],
                            ECon
                              (Some (Short "::"))
                              [EVar (Short "v4");
                              EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "update");
                                EVar (Short "v8")];
                                ELet
                                (Some "k")
                                (EApp
                                (Opn Minus)
                                [
                                EVar
                                (Short "v6");
                                ELit (IntLit 1)])
                                (EIf
                                (EApp
                                (Opb Lt)
                                [
                                EVar (Short "k");
                                ELit (IntLit 0)])
                                (ELit (IntLit 0))
                                (EVar (Short "k")))];
                                EVar (Short "v3")]])]))])))]
             "update");
           (Long "List" (Short "splitAtPki"),
           Recclosure
             {|
             sev := (Short "o",
                    Closure
                      {| sev := []; sec := [] |}
                      "v2"
                      (EFun "v3"
                         (EFun "v1"
                            (EApp Opapp
                               [EVar (Short "v2");
                               EApp Opapp
                                [
                                EVar
                                (Short "v3");
                                EVar (Short "v1")]]))))
                    :: nsEmpty;
             sec := nsEmpty |}
             [("splitAtPki", "v6",
              EFun "v7"
                (EFun "v8"
                   (EMat (EVar (Short "v8"))
                      [(Pcon (Some (Short "[]"))
                          [],
                       EApp Opapp
                         [EApp Opapp
                            [EVar (Short "v7");
                            ECon
                              (Some (Short "[]"))
                              []];
                         ECon (Some (Short "[]"))
                           []]);
                      (Pcon (Some (Short "::"))
                         [Pvar "v5"; Pvar "v4"],
                      EIf
                        (EApp Opapp
                           [EApp Opapp
                              [EVar (Short "v6");
                              ELit (IntLit 0)];
                           EVar (Short "v5")])
                        (EApp Opapp
                           [EApp Opapp
                              [EVar (Short "v7");
                              ECon
                                (Some
                                (Short "[]")) []];
                           ECon
                             (Some (Short "::"))
                             [EVar (Short "v5");
                             EVar (Short "v4")]])
                        (EApp Opapp
                           [EApp Opapp
                              [EApp Opapp
                                [
                                EVar
                                (Short
                                "splitAtPki");
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar (Short "o");
                                EVar (Short "v6")];
                                EFun "v1"
                                (EApp
                                (Opn Plus)
                                [
                                EVar
                                (Short "v1");
                                ELit (IntLit 1)])]];
                              EFun "v3"
                                (EFun "v2"
                                (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "v7");
                                ECon
                                (Some
                                (Short "::"))
                                [
                                EVar
                                (Short "v5");
                                EVar (Short "v3")]];
                                EVar (Short "v2")]))];
                           EVar (Short "v4")]))])))]
             "splitAtPki");
           (Long "List" (Short "front"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("front", "x0",
              EMat (EVar (Short "x0"))
                [(Pcon (Some (Short "[]")) [],
                 ERaise
                   (ECon (Some (Short "Bind")) []));
                (Pcon (Some (Short "::"))
                   [Pvar "v2"; Pvar "v1"],
                EIf
                  (EApp Equality
                     [EVar (Short "v1");
                     ECon (Some (Short "[]")) []])
                  (ECon (Some (Short "[]")) [])
                  (ECon (Some (Short "::"))
                     [EVar (Short "v2");
                     EApp Opapp
                       [EVar (Short "front");
                       EVar (Short "v1")]]))])]
             "front");
           (Long "List" (Short "isPrefix"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("isPrefix", "v5",
              EFun "v6"
                (EMat (EVar (Short "v5"))
                   [(Pcon (Some (Short "[]")) [],
                    EApp (Opb Leq)
                      [ELit (IntLit 0);
                      ELit (IntLit 0)]);
                   (Pcon (Some (Short "::"))
                      [Pvar "v4"; Pvar "v3"],
                   EMat (EVar (Short "v6"))
                     [(Pcon (Some (Short "[]"))
                         [],
                      EApp (Opb Lt)
                        [ELit (IntLit 0);
                        ELit (IntLit 0)]);
                     (Pcon (Some (Short "::"))
                        [Pvar "v2"; Pvar "v1"],
                     ELog And
                       (EApp Equality
                          [EVar (Short "v4");
                          EVar (Short "v2")])
                       (EApp Opapp
                          [EApp Opapp
                             [EVar
                                (Short "isPrefix");
                             EVar (Short "v3")];
                          EVar (Short "v1")]))])]))]
             "isPrefix");
           (Long "List" (Short "all_distinct"),
           Recclosure
             {|
             sev := (Short "member",
                    Recclosure
                      {|
                      sev := nsEmpty;
                      sec := nsEmpty |}
                      [("member", "v4",
                       EFun "v3"
                         (EMat
                            (EVar (Short "v3"))
                            [(Pcon
                                (Some
                                (Short "[]")) [],
                             EApp
                               (Opb Lt)
                               [ELit (IntLit 0);
                               ELit (IntLit 0)]);
                            (Pcon
                               (Some (Short "::"))
                               [Pvar "v2";
                               Pvar "v1"],
                            ELog Or
                              (EApp Equality
                                [
                                EVar
                                (Short "v4");
                                EVar (Short "v2")])
                              (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "member");
                                EVar (Short "v4")];
                                EVar (Short "v1")]))]))]
                      "member") :: nsEmpty;
             sec := nsEmpty |}
             [("all_distinct", "v3",
              EMat (EVar (Short "v3"))
                [(Pcon (Some (Short "[]")) [],
                 EApp (Opb Leq)
                   [ELit (IntLit 0);
                   ELit (IntLit 0)]);
                (Pcon (Some (Short "::"))
                   [Pvar "v2"; Pvar "v1"],
                ELog And
                  (EApp Equality
                     [EApp Opapp
                        [EApp Opapp
                           [EVar (Short "member");
                           EVar (Short "v2")];
                        EVar (Short "v1")];
                     EApp (Opb Lt)
                       [ELit (IntLit 0);
                       ELit (IntLit 0)]])
                  (EApp Opapp
                     [EVar (Short "all_distinct");
                     EVar (Short "v1")]))])]
             "all_distinct");
           (Long "List" (Short "pad_left"),
           Closure
             {|
             sev := (Short "genlist",
                    Closure
                      {|
                      sev := (Short "genlist_aux",
                             Recclosure
                               {|
                               sev := nsEmpty;
                               sec := nsEmpty |}
                               [("genlist_aux",
                                "v1",
                                EFun "v3"
                                (EFun "v2"
                                (EIf
                                (EApp Equality
                                [
                                EVar
                                (Short "v3");
                                ELit (IntLit 0)])
                                (EVar
                                (Short "v2"))
                                (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short
                                "genlist_aux");
                                EVar (Short "v1")];
                                ELet
                                (Some "k")
                                (EApp
                                (Opn Minus)
                                [
                                EVar
                                (Short "v3");
                                ELit (IntLit 1)])
                                (EIf
                                (EApp
                                (Opb Lt)
                                [
                                EVar (Short "k");
                                ELit (IntLit 0)])
                                (ELit (IntLit 0))
                                (EVar (Short "k")))];
                                ECon
                                (Some
                                (Short "::"))
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "v1");
                                ELet
                                (Some "k")
                                (EApp
                                (Opn Minus)
                                [
                                EVar
                                (Short "v3");
                                ELit (IntLit 1)])
                                (EIf
                                (EApp
                                (Opb Lt)
                                [
                                EVar (Short "k");
                                ELit (IntLit 0)])
                                (ELit (IntLit 0))
                                (EVar (Short "k")))];
                                EVar (Short "v2")]]))))]
                               "genlist_aux")
                             :: nsEmpty;
                      sec := nsEmpty |} "v1"
                      (EFun "v2"
                         (EApp Opapp
                            [EApp Opapp
                               [EApp Opapp
                                [
                                EVar
                                (Short
                                "genlist_aux");
                                EVar (Short "v1")];
                               EVar (Short "v2")];
                            ECon
                              (Some (Short "[]"))
                              []])))
                    :: (Short "const",
                       Closure
                         {|
                         sev := [];
                         sec := [] |} "v2"
                         (EFun "v1"
                            (EVar (Short "v2"))))
                       :: (Short "length",
                          Closure
                            {|
                            sev := (
                                Short
                                "length_aux",
                                Recclosure
                                {|
                                sev := nsEmpty;
                                sec := nsEmpty |}
                                [("length_aux",
                                "v3",
                                EFun "v4"
                                (EMat
                                (EVar
                                (Short "v3"))
                                [
                                (
                                Pcon
                                (Some
                                (Short "[]")) [],
                                EVar (Short "v4"));
                                (
                                Pcon
                                (Some
                                (Short "::"))
                                [
                                Pvar "v2";
                                Pvar "v1"],
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short
                                "length_aux");
                                EVar (Short "v1")];
                                EApp
                                (Opn Plus)
                                [
                                EVar
                                (Short "v4");
                                ELit (IntLit 1)]])]))]
                                "length_aux")
                                :: nsEmpty;
                            sec := nsEmpty |}
                            "v1"
                            (EApp Opapp
                               [EApp Opapp
                                [
                                EVar
                                (Short
                                "length_aux");
                                EVar (Short "v1")];
                               ELit (IntLit 0)]))
                          :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EFun "v2"
                (EFun "v3"
                   (EApp ListAppend
                      [EApp Opapp
                         [EApp Opapp
                            [EVar
                               (Short "genlist");
                            EApp Opapp
                              [EVar
                                (Short "const");
                              EVar (Short "v1")]];
                         ELet (Some "k")
                           (EApp
                              (Opn Minus)
                              [EVar (Short "v2");
                              EApp Opapp
                                [
                                EVar
                                (Short "length");
                                EVar (Short "v3")]])
                           (EIf
                              (EApp
                                (Opb Lt)
                                [
                                EVar (Short "k");
                                ELit (IntLit 0)])
                              (ELit (IntLit 0))
                              (EVar (Short "k")))];
                      EVar (Short "v3")]))));
           (Long "List" (Short "pad_right"),
           Closure
             {|
             sev := (Short "genlist",
                    Closure
                      {|
                      sev := (Short "genlist_aux",
                             Recclosure
                               {|
                               sev := nsEmpty;
                               sec := nsEmpty |}
                               [("genlist_aux",
                                "v1",
                                EFun "v3"
                                (EFun "v2"
                                (EIf
                                (EApp Equality
                                [
                                EVar
                                (Short "v3");
                                ELit (IntLit 0)])
                                (EVar
                                (Short "v2"))
                                (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short
                                "genlist_aux");
                                EVar (Short "v1")];
                                ELet
                                (Some "k")
                                (EApp
                                (Opn Minus)
                                [
                                EVar
                                (Short "v3");
                                ELit (IntLit 1)])
                                (EIf
                                (EApp
                                (Opb Lt)
                                [
                                EVar (Short "k");
                                ELit (IntLit 0)])
                                (ELit (IntLit 0))
                                (EVar (Short "k")))];
                                ECon
                                (Some
                                (Short "::"))
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "v1");
                                ELet
                                (Some "k")
                                (EApp
                                (Opn Minus)
                                [
                                EVar
                                (Short "v3");
                                ELit (IntLit 1)])
                                (EIf
                                (EApp
                                (Opb Lt)
                                [
                                EVar (Short "k");
                                ELit (IntLit 0)])
                                (ELit (IntLit 0))
                                (EVar (Short "k")))];
                                EVar (Short "v2")]]))))]
                               "genlist_aux")
                             :: nsEmpty;
                      sec := nsEmpty |} "v1"
                      (EFun "v2"
                         (EApp Opapp
                            [EApp Opapp
                               [EApp Opapp
                                [
                                EVar
                                (Short
                                "genlist_aux");
                                EVar (Short "v1")];
                               EVar (Short "v2")];
                            ECon
                              (Some (Short "[]"))
                              []])))
                    :: (Short "const",
                       Closure
                         {|
                         sev := [];
                         sec := [] |} "v2"
                         (EFun "v1"
                            (EVar (Short "v2"))))
                       :: (Short "length",
                          Closure
                            {|
                            sev := (
                                Short
                                "length_aux",
                                Recclosure
                                {|
                                sev := nsEmpty;
                                sec := nsEmpty |}
                                [("length_aux",
                                "v3",
                                EFun "v4"
                                (EMat
                                (EVar
                                (Short "v3"))
                                [
                                (
                                Pcon
                                (Some
                                (Short "[]")) [],
                                EVar (Short "v4"));
                                (
                                Pcon
                                (Some
                                (Short "::"))
                                [
                                Pvar "v2";
                                Pvar "v1"],
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short
                                "length_aux");
                                EVar (Short "v1")];
                                EApp
                                (Opn Plus)
                                [
                                EVar
                                (Short "v4");
                                ELit (IntLit 1)]])]))]
                                "length_aux")
                                :: nsEmpty;
                            sec := nsEmpty |}
                            "v1"
                            (EApp Opapp
                               [EApp Opapp
                                [
                                EVar
                                (Short
                                "length_aux");
                                EVar (Short "v1")];
                               ELit (IntLit 0)]))
                          :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EFun "v2"
                (EFun "v3"
                   (EApp ListAppend
                      [EVar (Short "v3");
                      EApp Opapp
                        [EApp Opapp
                           [EVar
                              (Short "genlist");
                           EApp Opapp
                             [EVar
                                (Short "const");
                             EVar (Short "v1")]];
                        ELet (Some "k")
                          (EApp (Opn Minus)
                             [EVar (Short "v2");
                             EApp Opapp
                               [EVar
                                (Short "length");
                               EVar (Short "v3")]])
                          (EIf
                             (EApp
                                (Opb Lt)
                                [
                                EVar (Short "k");
                                ELit (IntLit 0)])
                             (ELit (IntLit 0))
                             (EVar (Short "k")))]]))));
           (Long "List" (Short "unzip"),
           Recclosure
             {|
             sev := (Short "fst",
                    Closure
                      {| sev := []; sec := [] |}
                      "v3"
                      (EMat (EVar (Short "v3"))
                         [(Pcon None
                             [Pvar "v2";
                             Pvar "v1"],
                          EVar (Short "v2"))]))
                    :: (Short "fst",
                       Closure
                         {|
                         sev := [];
                         sec := [] |} "v3"
                         (EMat
                            (EVar (Short "v3"))
                            [(Pcon None
                                [
                                Pvar "v2";
                                Pvar "v1"],
                             EVar (Short "v2"))]))
                       :: (Short "snd",
                          Closure
                            {|
                            sev := [];
                            sec := [] |} "v3"
                            (EMat
                               (EVar (Short "v3"))
                               [(
                                Pcon None
                                [
                                Pvar "v2";
                                Pvar "v1"],
                                EVar (Short "v1"))]))
                          :: (Short "snd",
                             Closure
                               {|
                               sev := [];
                               sec := [] |} "v3"
                               (EMat
                                (EVar
                                (Short "v3"))
                                [(
                                Pcon None
                                [
                                Pvar "v2";
                                Pvar "v1"],
                                EVar (Short "v1"))]))
                             :: nsEmpty;
             sec := nsEmpty |}
             [("unzip", "v3",
              EMat (EVar (Short "v3"))
                [(Pcon (Some (Short "[]")) [],
                 ECon None
                   [ECon (Some (Short "[]")) [];
                   ECon (Some (Short "[]")) []]);
                (Pcon (Some (Short "::"))
                   [Pvar "v2"; Pvar "v1"],
                ECon None
                  [ECon (Some (Short "::"))
                     [EApp Opapp
                        [EVar (Short "fst");
                        EVar (Short "v2")];
                     EApp Opapp
                       [EVar (Short "fst");
                       EApp Opapp
                         [EVar (Short "unzip");
                         EVar (Short "v1")]]];
                  ECon (Some (Short "::"))
                    [EApp Opapp
                       [EVar (Short "snd");
                       EVar (Short "v2")];
                    EApp Opapp
                      [EVar (Short "snd");
                      EApp Opapp
                        [EVar (Short "unzip");
                        EVar (Short "v1")]]]])])]
             "unzip");
           (Long "List" (Short "sum"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("sum", "v3",
              EMat (EVar (Short "v3"))
                [(Pcon (Some (Short "[]")) [],
                 ELit (IntLit 0));
                (Pcon (Some (Short "::"))
                   [Pvar "v2"; Pvar "v1"],
                EApp (Opn Plus)
                  [EVar (Short "v2");
                  EApp Opapp
                    [EVar (Short "sum");
                    EVar (Short "v1")]])])] "sum");
           (Long "List" (Short "member"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("member", "v4",
              EFun "v3"
                (EMat (EVar (Short "v3"))
                   [(Pcon (Some (Short "[]")) [],
                    EApp (Opb Lt)
                      [ELit (IntLit 0);
                      ELit (IntLit 0)]);
                   (Pcon (Some (Short "::"))
                      [Pvar "v2"; Pvar "v1"],
                   ELog Or
                     (EApp Equality
                        [EVar (Short "v4");
                        EVar (Short "v2")])
                     (EApp Opapp
                        [EApp Opapp
                           [EVar (Short "member");
                           EVar (Short "v4")];
                        EVar (Short "v1")]))]))]
             "member");
           (Long "List" (Short "zip"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("zip", "v9",
              EMat (EVar (Short "v9"))
                [(Pcon None
                    [Pvar "v8"; Pvar "v7"],
                 EMat (EVar (Short "v8"))
                   [(Pcon (Some (Short "[]")) [],
                    EMat (EVar (Short "v7"))
                      [(Pcon (Some (Short "[]"))
                          [],
                       ECon (Some (Short "[]"))
                         []);
                      (Pcon (Some (Short "::"))
                         [Pvar "v2"; Pvar "v1"],
                      ECon (Some (Short "[]")) [])]);
                   (Pcon (Some (Short "::"))
                      [Pvar "v6"; Pvar "v5"],
                   EMat (EVar (Short "v7"))
                     [(Pcon (Some (Short "[]"))
                         [],
                      ECon (Some (Short "[]")) []);
                     (Pcon (Some (Short "::"))
                        [Pvar "v4"; Pvar "v3"],
                     ECon (Some (Short "::"))
                       [ECon None
                          [EVar (Short "v6");
                          EVar (Short "v4")];
                       EApp Opapp
                         [EVar (Short "zip");
                         ECon None
                           [EVar (Short "v5");
                           EVar (Short "v3")]]])])])])]
             "zip");
           (Long "List" (Short "collate"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("collate", "v7",
              EFun "v8"
                (EFun "v9"
                   (EMat (EVar (Short "v8"))
                      [(Pcon (Some (Short "[]"))
                          [],
                       EMat (EVar (Short "v9"))
                         [(Pcon
                             (Some (Short "[]"))
                             [],
                          ECon
                            (Some (Short "Equal"))
                            []);
                         (Pcon
                            (Some (Short "::"))
                            [Pvar "v2";
                            Pvar "v1"],
                         ECon
                           (Some (Short "Less"))
                           [])]);
                      (Pcon (Some (Short "::"))
                         [Pvar "v6"; Pvar "v5"],
                      EMat (EVar (Short "v9"))
                        [(Pcon
                            (Some (Short "[]"))
                            [],
                         ECon
                           (Some
                              (Short "Greater"))
                           []);
                        (Pcon (Some (Short "::"))
                           [Pvar "v4"; Pvar "v3"],
                        EIf
                          (EApp Equality
                             [EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "v7");
                                EVar (Short "v6")];
                                EVar (Short "v4")];
                             ECon
                               (Some
                                (Short "Equal"))
                               []])
                          (EApp Opapp
                             [EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "collate");
                                EVar (Short "v7")];
                                EVar (Short "v5")];
                             EVar (Short "v3")])
                          (EApp Opapp
                             [EApp Opapp
                                [
                                EVar
                                (Short "v7");
                                EVar (Short "v6")];
                             EVar (Short "v4")]))])])))]
             "collate");
           (Long "List" (Short "tabulate"),
           Closure
             {|
             sev := (Short "tabulate",
                    Recclosure
                      {|
                      sev := (Short "rev",
                             Closure
                               {|
                               sev := (
                                Short "rev",
                                Recclosure
                                {|
                                sev := nsEmpty;
                                sec := nsEmpty |}
                                [("rev", "v4",
                                EFun "v3"
                                (EMat
                                (EVar
                                (Short "v4"))
                                [
                                (
                                Pcon
                                (Some
                                (Short "[]")) [],
                                EVar (Short "v3"));
                                (
                                Pcon
                                (Some
                                (Short "::"))
                                [
                                Pvar "v2";
                                Pvar "v1"],
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "rev");
                                EVar (Short "v1")];
                                ECon
                                (Some
                                (Short "::"))
                                [
                                EVar
                                (Short "v2");
                                EVar (Short "v3")]])]))]
                                "rev") :: nsEmpty;
                               sec := nsEmpty |}
                               "v1"
                               (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "rev");
                                EVar (Short "v1")];
                                ECon
                                (Some
                                (Short "[]")) []]))
                             :: nsEmpty;
                      sec := nsEmpty |}
                      [("tabulate", "v8",
                       EFun "v7"
                         (EFun "v6"
                            (EFun "v5"
                               (ELet
                                (Some "v4")
                                (EApp
                                (Opb Geq)
                                [
                                EVar
                                (Short "v8");
                                EVar (Short "v7")])
                                (EIf
                                (EVar
                                (Short "v4"))
                                (EApp Opapp
                                [
                                EVar
                                (Short "rev");
                                EVar (Short "v5")])
                                (ELet
                                (Some "v3")
                                (EApp Opapp
                                [
                                EVar
                                (Short "v6");
                                EVar (Short "v8")])
                                (ELet
                                (Some "v2")
                                (EApp
                                (Opn Plus)
                                [
                                EVar
                                (Short "v8");
                                ELit (IntLit 1)])
                                (ELet
                                (Some "v1")
                                (ECon
                                (Some
                                (Short "::"))
                                [
                                EVar
                                (Short "v3");
                                EVar (Short "v5")])
                                (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "tabulate");
                                EVar (Short "v2")];
                                EVar (Short "v7")];
                                EVar (Short "v6")];
                                EVar (Short "v1")])))))))))]
                      "tabulate") :: nsEmpty;
             sec := nsEmpty |} "v3"
             (EFun "v2"
                (ELet (Some "v1")
                   (ECon (Some (Short "[]")) [])
                   (EApp Opapp
                      [EApp Opapp
                         [EApp Opapp
                            [EApp Opapp
                               [EVar
                                (Short "tabulate");
                               ELit (IntLit 0)];
                            EVar (Short "v3")];
                         EVar (Short "v2")];
                      EVar (Short "v1")]))));
           (Long "List" (Short "tabulate"),
           Recclosure
             {|
             sev := (Short "rev",
                    Closure
                      {|
                      sev := (Short "rev",
                             Recclosure
                               {|
                               sev := nsEmpty;
                               sec := nsEmpty |}
                               [("rev", "v4",
                                EFun "v3"
                                (EMat
                                (EVar
                                (Short "v4"))
                                [
                                (
                                Pcon
                                (Some
                                (Short "[]")) [],
                                EVar (Short "v3"));
                                (
                                Pcon
                                (Some
                                (Short "::"))
                                [
                                Pvar "v2";
                                Pvar "v1"],
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "rev");
                                EVar (Short "v1")];
                                ECon
                                (Some
                                (Short "::"))
                                [
                                EVar
                                (Short "v2");
                                EVar (Short "v3")]])]))]
                               "rev") :: nsEmpty;
                      sec := nsEmpty |} "v1"
                      (EApp Opapp
                         [EApp Opapp
                            [EVar (Short "rev");
                            EVar (Short "v1")];
                         ECon (Some (Short "[]"))
                           []])) :: nsEmpty;
             sec := nsEmpty |}
             [("tabulate", "v8",
              EFun "v7"
                (EFun "v6"
                   (EFun "v5"
                      (ELet (Some "v4")
                         (EApp (Opb Geq)
                            [EVar (Short "v8");
                            EVar (Short "v7")])
                         (EIf (EVar (Short "v4"))
                            (EApp Opapp
                               [EVar
                                (Short "rev");
                               EVar (Short "v5")])
                            (ELet
                               (Some "v3")
                               (EApp Opapp
                                [
                                EVar
                                (Short "v6");
                                EVar (Short "v8")])
                               (ELet
                                (Some "v2")
                                (EApp
                                (Opn Plus)
                                [
                                EVar
                                (Short "v8");
                                ELit (IntLit 1)])
                                (ELet
                                (Some "v1")
                                (ECon
                                (Some
                                (Short "::"))
                                [
                                EVar
                                (Short "v3");
                                EVar (Short "v5")])
                                (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "tabulate");
                                EVar (Short "v2")];
                                EVar (Short "v7")];
                                EVar (Short "v6")];
                                EVar (Short "v1")])))))))))]
             "tabulate");
           (Long "List" (Short "genlist"),
           Closure
             {|
             sev := (Short "genlist_aux",
                    Recclosure
                      {|
                      sev := nsEmpty;
                      sec := nsEmpty |}
                      [("genlist_aux", "v1",
                       EFun "v3"
                         (EFun "v2"
                            (EIf
                               (EApp Equality
                                [
                                EVar
                                (Short "v3");
                                ELit (IntLit 0)])
                               (EVar (Short "v2"))
                               (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short
                                "genlist_aux");
                                EVar (Short "v1")];
                                ELet
                                (Some "k")
                                (EApp
                                (Opn Minus)
                                [
                                EVar
                                (Short "v3");
                                ELit (IntLit 1)])
                                (EIf
                                (EApp
                                (Opb Lt)
                                [
                                EVar (Short "k");
                                ELit (IntLit 0)])
                                (ELit (IntLit 0))
                                (EVar (Short "k")))];
                                ECon
                                (Some
                                (Short "::"))
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "v1");
                                ELet
                                (Some "k")
                                (EApp
                                (Opn Minus)
                                [
                                EVar
                                (Short "v3");
                                ELit (IntLit 1)])
                                (EIf
                                (EApp
                                (Opb Lt)
                                [
                                EVar (Short "k");
                                ELit (IntLit 0)])
                                (ELit (IntLit 0))
                                (EVar (Short "k")))];
                                EVar (Short "v2")]]))))]
                      "genlist_aux") :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EFun "v2"
                (EApp Opapp
                   [EApp Opapp
                      [EApp Opapp
                         [EVar
                            (Short "genlist_aux");
                         EVar (Short "v1")];
                      EVar (Short "v2")];
                   ECon (Some (Short "[]")) []])));
           (Long "List" (Short "snoc"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("snoc", "v4",
              EFun "v3"
                (EMat (EVar (Short "v3"))
                   [(Pcon (Some (Short "[]")) [],
                    ECon (Some (Short "::"))
                      [EVar (Short "v4");
                      ECon (Some (Short "[]")) []]);
                   (Pcon (Some (Short "::"))
                      [Pvar "v2"; Pvar "v1"],
                   ECon (Some (Short "::"))
                     [EVar (Short "v2");
                     EApp Opapp
                       [EApp Opapp
                          [EVar (Short "snoc");
                          EVar (Short "v4")];
                       EVar (Short "v1")]])]))]
             "snoc");
           (Long "List" (Short "all"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("all", "v3",
              EFun "v4"
                (EMat (EVar (Short "v4"))
                   [(Pcon (Some (Short "[]")) [],
                    EApp (Opb Leq)
                      [ELit (IntLit 0);
                      ELit (IntLit 0)]);
                   (Pcon (Some (Short "::"))
                      [Pvar "v2"; Pvar "v1"],
                   ELog And
                     (EApp Opapp
                        [EVar (Short "v3");
                        EVar (Short "v2")])
                     (EApp Opapp
                        [EApp Opapp
                           [EVar (Short "all");
                           EVar (Short "v3")];
                        EVar (Short "v1")]))]))]
             "all");
           (Long "List" (Short "exists"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("exists", "v3",
              EFun "v4"
                (EMat (EVar (Short "v4"))
                   [(Pcon (Some (Short "[]")) [],
                    EApp (Opb Lt)
                      [ELit (IntLit 0);
                      ELit (IntLit 0)]);
                   (Pcon (Some (Short "::"))
                      [Pvar "v2"; Pvar "v1"],
                   ELog Or
                     (EApp Opapp
                        [EVar (Short "v3");
                        EVar (Short "v2")])
                     (EApp Opapp
                        [EApp Opapp
                           [EVar (Short "exists");
                           EVar (Short "v3")];
                        EVar (Short "v1")]))]))]
             "exists");
           (Long "List" (Short "foldri"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("foldri", "v5",
              EFun "v4"
                (EFun "v6"
                   (EMat (EVar (Short "v6"))
                      [(Pcon (Some (Short "[]"))
                          [], EVar (Short "v4"));
                      (Pcon (Some (Short "::"))
                         [Pvar "v3"; Pvar "v2"],
                      EApp Opapp
                        [EApp Opapp
                           [EApp Opapp
                              [EVar (Short "v5");
                              ELit (IntLit 0)];
                           EVar (Short "v3")];
                        EApp Opapp
                          [EApp Opapp
                             [EApp Opapp
                                [
                                EVar
                                (Short "foldri");
                                EFun "v1"
                                (EApp Opapp
                                [
                                EVar
                                (Short "v5");
                                EApp
                                (Opn Plus)
                                [
                                EVar
                                (Short "v1");
                                ELit (IntLit 1)]])];
                             EVar (Short "v4")];
                          EVar (Short "v2")]])])))]
             "foldri");
           (Long "List" (Short "foldr"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("foldr", "v4",
              EFun "v3"
                (EFun "v5"
                   (EMat (EVar (Short "v5"))
                      [(Pcon (Some (Short "[]"))
                          [], EVar (Short "v3"));
                      (Pcon (Some (Short "::"))
                         [Pvar "v2"; Pvar "v1"],
                      EApp Opapp
                        [EApp Opapp
                           [EVar (Short "v4");
                           EVar (Short "v2")];
                        EApp Opapp
                          [EApp Opapp
                             [EApp Opapp
                                [
                                EVar
                                (Short "foldr");
                                EVar (Short "v4")];
                             EVar (Short "v3")];
                          EVar (Short "v1")]])])))]
             "foldr");
           (Long "List" (Short "foldi"),
           Closure
             {|
             sev := (Short "foldli_aux",
                    Recclosure
                      {|
                      sev := nsEmpty;
                      sec := nsEmpty |}
                      [("foldli_aux", "v4",
                       EFun "v3"
                         (EFun "v5"
                            (EFun "v6"
                               (EMat
                                (EVar
                                (Short "v6"))
                                [
                                (
                                Pcon
                                (Some
                                (Short "[]")) [],
                                EVar (Short "v3"));
                                (
                                Pcon
                                (Some
                                (Short "::"))
                                [
                                Pvar "v2";
                                Pvar "v1"],
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short
                                "foldli_aux");
                                EVar (Short "v4")];
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "v4");
                                EVar (Short "v5")];
                                EVar (Short "v2")];
                                EVar (Short "v3")]];
                                EApp
                                (Opn Plus)
                                [
                                EVar
                                (Short "v5");
                                ELit (IntLit 1)]];
                                EVar (Short "v1")])]))))]
                      "foldli_aux") :: nsEmpty;
             sec := nsEmpty |} "v2"
             (EFun "v1"
                (EFun "v3"
                   (EApp Opapp
                      [EApp Opapp
                         [EApp Opapp
                            [EApp Opapp
                               [EVar
                                (Short
                                "foldli_aux");
                               EVar (Short "v2")];
                            EVar (Short "v1")];
                         ELit (IntLit 0)];
                      EVar (Short "v3")]))));
           (Long "List" (Short "foldl"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("foldl", "v4",
              EFun "v3"
                (EFun "v5"
                   (EMat (EVar (Short "v5"))
                      [(Pcon (Some (Short "[]"))
                          [], EVar (Short "v3"));
                      (Pcon (Some (Short "::"))
                         [Pvar "v2"; Pvar "v1"],
                      EApp Opapp
                        [EApp Opapp
                           [EApp Opapp
                              [EVar
                                (Short "foldl");
                              EVar (Short "v4")];
                           EApp Opapp
                             [EApp Opapp
                                [
                                EVar
                                (Short "v4");
                                EVar (Short "v3")];
                             EVar (Short "v2")]];
                        EVar (Short "v1")])])))]
             "foldl");
           (Long "List" (Short "partition"),
           Closure
             {|
             sev := (Short "partition_aux",
                    Recclosure
                      {|
                      sev := (Short "rev",
                             Closure
                               {|
                               sev := (
                                Short "rev",
                                Recclosure
                                {|
                                sev := nsEmpty;
                                sec := nsEmpty |}
                                [("rev", "v4",
                                EFun "v3"
                                (EMat
                                (EVar
                                (Short "v4"))
                                [
                                (
                                Pcon
                                (Some
                                (Short "[]")) [],
                                EVar (Short "v3"));
                                (
                                Pcon
                                (Some
                                (Short "::"))
                                [
                                Pvar "v2";
                                Pvar "v1"],
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "rev");
                                EVar (Short "v1")];
                                ECon
                                (Some
                                (Short "::"))
                                [
                                EVar
                                (Short "v2");
                                EVar (Short "v3")]])]))]
                                "rev") :: nsEmpty;
                               sec := nsEmpty |}
                               "v1"
                               (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "rev");
                                EVar (Short "v1")];
                                ECon
                                (Some
                                (Short "[]")) []]))
                             :: (
                                Short "rev",
                                Closure
                                {|
                                sev := (
                                Short "rev",
                                Recclosure
                                {|
                                sev := nsEmpty;
                                sec := nsEmpty |}
                                [("rev", "v4",
                                EFun "v3"
                                (EMat
                                (EVar
                                (Short "v4"))
                                [
                                (
                                Pcon
                                (Some
                                (Short "[]")) [],
                                EVar (Short "v3"));
                                (
                                Pcon
                                (Some
                                (Short "::"))
                                [
                                Pvar "v2";
                                Pvar "v1"],
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "rev");
                                EVar (Short "v1")];
                                ECon
                                (Some
                                (Short "::"))
                                [
                                EVar
                                (Short "v2");
                                EVar (Short "v3")]])]))]
                                "rev") :: nsEmpty;
                                sec := nsEmpty |}
                                "v1"
                                (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "rev");
                                EVar (Short "v1")];
                                ECon
                                (Some
                                (Short "[]")) []]))
                                :: nsEmpty;
                      sec := nsEmpty |}
                      [("partition_aux", "v3",
                       EFun "v5"
                         (EFun "v6"
                            (EFun "v4"
                               (EMat
                                (EVar
                                (Short "v5"))
                                [
                                (
                                Pcon
                                (Some
                                (Short "[]")) [],
                                ECon None
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "rev");
                                EVar (Short "v6")];
                                EApp Opapp
                                [
                                EVar
                                (Short "rev");
                                EVar (Short "v4")]]);
                                (
                                Pcon
                                (Some
                                (Short "::"))
                                [
                                Pvar "v2";
                                Pvar "v1"],
                                EIf
                                (EApp Opapp
                                [
                                EVar
                                (Short "v3");
                                EVar (Short "v2")])
                                (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short
                                "partition_aux");
                                EVar (Short "v3")];
                                EVar (Short "v1")];
                                ECon
                                (Some
                                (Short "::"))
                                [
                                EVar
                                (Short "v2");
                                EVar (Short "v6")]];
                                EVar (Short "v4")])
                                (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short
                                "partition_aux");
                                EVar (Short "v3")];
                                EVar (Short "v1")];
                                EVar (Short "v6")];
                                ECon
                                (Some
                                (Short "::"))
                                [
                                EVar
                                (Short "v2");
                                EVar (Short "v4")]]))]))))]
                      "partition_aux") :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EFun "v2"
                (EApp Opapp
                   [EApp Opapp
                      [EApp Opapp
                         [EApp Opapp
                            [EVar
                               (Short
                                "partition_aux");
                            EVar (Short "v1")];
                         EVar (Short "v2")];
                      ECon (Some (Short "[]")) []];
                   ECon (Some (Short "[]")) []])));
           (Long "List" (Short "filter"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("filter", "v3",
              EFun "v4"
                (EMat (EVar (Short "v4"))
                   [(Pcon (Some (Short "[]")) [],
                    ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::"))
                      [Pvar "v2"; Pvar "v1"],
                   EIf
                     (EApp Opapp
                        [EVar (Short "v3");
                        EVar (Short "v2")])
                     (ECon (Some (Short "::"))
                        [EVar (Short "v2");
                        EApp Opapp
                          [EApp Opapp
                             [EVar
                                (Short "filter");
                             EVar (Short "v3")];
                          EVar (Short "v1")]])
                     (EApp Opapp
                        [EApp Opapp
                           [EVar (Short "filter");
                           EVar (Short "v3")];
                        EVar (Short "v1")]))]))]
             "filter");
           (Long "List" (Short "find"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("find", "v3",
              EFun "v4"
                (EMat (EVar (Short "v4"))
                   [(Pcon (Some (Short "[]")) [],
                    ECon (Some (Short "None")) []);
                   (Pcon (Some (Short "::"))
                      [Pvar "v2"; Pvar "v1"],
                   EIf
                     (EApp Opapp
                        [EVar (Short "v3");
                        EVar (Short "v2")])
                     (ECon (Some (Short "Some"))
                        [EVar (Short "v2")])
                     (EApp Opapp
                        [EApp Opapp
                           [EVar (Short "find");
                           EVar (Short "v3")];
                        EVar (Short "v1")]))]))]
             "find");
           (Long "List" (Short "app"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("app", "f",
              EFun "ls"
                (EMat (EVar (Short "ls"))
                   [(Pcon (Some (Short "[]")) [],
                    ECon None []);
                   (Pcon (Some (Short "::"))
                      [Pvar "x"; Pvar "xs"],
                   ELet None
                     (EApp Opapp
                        [EVar (Short "f");
                        EVar (Short "x")])
                     (EApp Opapp
                        [EApp Opapp
                           [EVar (Short "app");
                           EVar (Short "f")];
                        EVar (Short "xs")]))]))]
             "app");
           (Long "List" (Short "mapPartial"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("mapPartial", "v4",
              EFun "v5"
                (EMat (EVar (Short "v5"))
                   [(Pcon (Some (Short "[]")) [],
                    ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::"))
                      [Pvar "v3"; Pvar "v2"],
                   EMat
                     (EApp Opapp
                        [EVar (Short "v4");
                        EVar (Short "v3")])
                     [(Pcon (Some (Short "None"))
                         [],
                      EApp Opapp
                        [EApp Opapp
                           [EVar
                              (Short "mapPartial");
                           EVar (Short "v4")];
                        EVar (Short "v2")]);
                     (Pcon (Some (Short "Some"))
                        [Pvar "v1"],
                     ECon (Some (Short "::"))
                       [EVar (Short "v1");
                       EApp Opapp
                         [EApp Opapp
                            [EVar
                               (Short
                                "mapPartial");
                            EVar (Short "v4")];
                         EVar (Short "v2")]])])]))]
             "mapPartial");
           (Long "List" (Short "mapi"),
           Closure
             {|
             sev := (Short "mapi",
                    Recclosure
                      {|
                      sev := nsEmpty;
                      sec := nsEmpty |}
                      [("mapi", "v4",
                       EFun "v5"
                         (EFun "v6"
                            (EMat
                               (EVar (Short "v6"))
                               [(
                                Pcon
                                (Some
                                (Short "[]")) [],
                                ECon
                                (Some
                                (Short "[]")) []);
                               (Pcon
                                (Some
                                (Short "::"))
                                [
                                Pvar "v3";
                                Pvar "v2"],
                               ELet
                                (Some "v1")
                                (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "v4");
                                EVar (Short "v5")];
                                EVar (Short "v3")])
                                (ECon
                                (Some
                                (Short "::"))
                                [
                                EVar
                                (Short "v1");
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "mapi");
                                EVar (Short "v4")];
                                EApp
                                (Opn Plus)
                                [
                                EVar
                                (Short "v5");
                                ELit (IntLit 1)]];
                                EVar (Short "v2")]]))])))]
                      "mapi") :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EFun "v2"
                (EApp Opapp
                   [EApp Opapp
                      [EApp Opapp
                         [EVar (Short "mapi");
                         EVar (Short "v1")];
                      ELit (IntLit 0)];
                   EVar (Short "v2")])));
           (Long "List" (Short "map"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("map", "v4",
              EFun "v5"
                (EMat (EVar (Short "v5"))
                   [(Pcon (Some (Short "[]")) [],
                    ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::"))
                      [Pvar "v3"; Pvar "v2"],
                   ELet (Some "v1")
                     (EApp Opapp
                        [EVar (Short "v4");
                        EVar (Short "v3")])
                     (ECon (Some (Short "::"))
                        [EVar (Short "v1");
                        EApp Opapp
                          [EApp Opapp
                             [EVar (Short "map");
                             EVar (Short "v4")];
                          EVar (Short "v2")]]))]))]
             "map");
           (Long "List" (Short "concat"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("concat", "v3",
              EMat (EVar (Short "v3"))
                [(Pcon (Some (Short "[]")) [],
                 ECon (Some (Short "[]")) []);
                (Pcon (Some (Short "::"))
                   [Pvar "v2"; Pvar "v1"],
                EApp ListAppend
                  [EVar (Short "v2");
                  EApp Opapp
                    [EVar (Short "concat");
                    EVar (Short "v1")]])])]
             "concat");
           (Long "List" (Short "cmp"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("cmp", "v7",
              EFun "v8"
                (EFun "v9"
                   (EMat (EVar (Short "v8"))
                      [(Pcon (Some (Short "[]"))
                          [],
                       EMat (EVar (Short "v9"))
                         [(Pcon
                             (Some (Short "[]"))
                             [],
                          ECon
                            (Some (Short "Equal"))
                            []);
                         (Pcon
                            (Some (Short "::"))
                            [Pvar "v2";
                            Pvar "v1"],
                         ECon
                           (Some (Short "Less"))
                           [])]);
                      (Pcon (Some (Short "::"))
                         [Pvar "v6"; Pvar "v5"],
                      EMat (EVar (Short "v9"))
                        [(Pcon
                            (Some (Short "[]"))
                            [],
                         ECon
                           (Some
                              (Short "Greater"))
                           []);
                        (Pcon (Some (Short "::"))
                           [Pvar "v4"; Pvar "v3"],
                        EMat
                          (EApp Opapp
                             [EApp Opapp
                                [
                                EVar
                                (Short "v7");
                                EVar (Short "v6")];
                             EVar (Short "v4")])
                          [(Pcon
                              (Some
                                (Short "Less"))
                              [],
                           ECon
                             (Some (Short "Less"))
                             []);
                          (Pcon
                             (Some
                                (Short "Equal"))
                             [],
                          EApp Opapp
                            [EApp Opapp
                               [EApp Opapp
                                [
                                EVar
                                (Short "cmp");
                                EVar (Short "v7")];
                               EVar (Short "v5")];
                            EVar (Short "v3")]);
                          (Pcon
                             (Some
                                (Short "Greater"))
                             [],
                          ECon
                            (Some
                               (Short "Greater"))
                            [])])])])))] "cmp");
           (Long "List" (Short "dropUntil"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("dropUntil", "v3",
              EFun "v4"
                (EMat (EVar (Short "v4"))
                   [(Pcon (Some (Short "[]")) [],
                    ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::"))
                      [Pvar "v2"; Pvar "v1"],
                   EIf
                     (EApp Opapp
                        [EVar (Short "v3");
                        EVar (Short "v2")])
                     (ECon (Some (Short "::"))
                        [EVar (Short "v2");
                        EVar (Short "v1")])
                     (EApp Opapp
                        [EApp Opapp
                           [EVar
                              (Short "dropUntil");
                           EVar (Short "v3")];
                        EVar (Short "v1")]))]))]
             "dropUntil");
           (Long "List" (Short "takeUntil"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("takeUntil", "v3",
              EFun "v4"
                (EMat (EVar (Short "v4"))
                   [(Pcon (Some (Short "[]")) [],
                    ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::"))
                      [Pvar "v2"; Pvar "v1"],
                   EIf
                     (EApp Opapp
                        [EVar (Short "v3");
                        EVar (Short "v2")])
                     (ECon (Some (Short "[]")) [])
                     (ECon (Some (Short "::"))
                        [EVar (Short "v2");
                        EApp Opapp
                          [EApp Opapp
                             [EVar
                                (Short
                                "takeUntil");
                             EVar (Short "v3")];
                          EVar (Short "v1")]]))]))]
             "takeUntil");
           (Long "List" (Short "drop"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("drop", "v3",
              EFun "v4"
                (EMat (EVar (Short "v3"))
                   [(Pcon (Some (Short "[]")) [],
                    ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::"))
                      [Pvar "v2"; Pvar "v1"],
                   EIf
                     (EApp Equality
                        [EVar (Short "v4");
                        ELit (IntLit 0)])
                     (ECon (Some (Short "::"))
                        [EVar (Short "v2");
                        EVar (Short "v1")])
                     (EApp Opapp
                        [EApp Opapp
                           [EVar (Short "drop");
                           EVar (Short "v1")];
                        ELet (Some "k")
                          (EApp (Opn Minus)
                             [EVar (Short "v4");
                             ELit (IntLit 1)])
                          (EIf
                             (EApp
                                (Opb Lt)
                                [
                                EVar (Short "k");
                                ELit (IntLit 0)])
                             (ELit (IntLit 0))
                             (EVar (Short "k")))]))]))]
             "drop");
           (Long "List" (Short "take"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("take", "v3",
              EFun "v4"
                (EMat (EVar (Short "v3"))
                   [(Pcon (Some (Short "[]")) [],
                    ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::"))
                      [Pvar "v2"; Pvar "v1"],
                   EIf
                     (EApp Equality
                        [EVar (Short "v4");
                        ELit (IntLit 0)])
                     (ECon (Some (Short "[]")) [])
                     (ECon (Some (Short "::"))
                        [EVar (Short "v2");
                        EApp Opapp
                          [EApp Opapp
                             [EVar (Short "take");
                             EVar (Short "v1")];
                          ELet (Some "k")
                            (EApp
                               (Opn Minus)
                               [EVar (Short "v4");
                               ELit (IntLit 1)])
                            (EIf
                               (EApp
                                (Opb Lt)
                                [
                                EVar (Short "k");
                                ELit (IntLit 0)])
                               (ELit (IntLit 0))
                               (EVar (Short "k")))]]))]))]
             "take");
           (Long "List" (Short "nth"),
           Recclosure
             {|
             sev := (Short "hd",
                    Closure
                      {|
                      sev := nsEmpty;
                      sec := nsEmpty |} "x0"
                      (EMat (EVar (Short "x0"))
                         [(Pcon
                             (Some (Short "[]"))
                             [],
                          ERaise
                            (ECon
                               (Some
                                (Short "Bind"))
                               []));
                         (Pcon
                            (Some (Short "::"))
                            [Pvar "v2";
                            Pvar "v1"],
                         EVar (Short "v2"))]))
                    :: (Short "tl",
                       Closure
                         {|
                         sev := nsEmpty;
                         sec := nsEmpty |} "v3"
                         (EMat
                            (EVar (Short "v3"))
                            [(Pcon
                                (Some
                                (Short "[]")) [],
                             ECon
                               (Some (Short "[]"))
                               []);
                            (Pcon
                               (Some (Short "::"))
                               [Pvar "v2";
                               Pvar "v1"],
                            EVar (Short "v1"))]))
                       :: nsEmpty;
             sec := nsEmpty |}
             [("nth", "v1",
              EFun "v2"
                (EIf
                   (EApp Equality
                      [EVar (Short "v2");
                      ELit (IntLit 0)])
                   (EApp Opapp
                      [EVar (Short "hd");
                      EVar (Short "v1")])
                   (EApp Opapp
                      [EApp Opapp
                         [EVar (Short "nth");
                         EApp Opapp
                           [EVar (Short "tl");
                           EVar (Short "v1")]];
                      ELet (Some "k")
                        (EApp (Opn Minus)
                           [EVar (Short "v2");
                           ELit (IntLit 1)])
                        (EIf
                           (EApp
                              (Opb Lt)
                              [EVar (Short "k");
                              ELit (IntLit 0)])
                           (ELit (IntLit 0))
                           (EVar (Short "k")))])))]
             "nth");
           (Long "List" (Short "getItem"),
           Closure
             {|
             sev := nsEmpty;
             sec := (Short "None",
                    (0%nat, TypeStamp "None" 0))
                    :: (Short "Some",
                       (1%nat,
                       TypeStamp "Some" 0))
                       :: nsEmpty |} "v3"
             (EMat (EVar (Short "v3"))
                [(Pcon (Some (Short "[]")) [],
                 ECon (Some (Short "None")) []);
                (Pcon (Some (Short "::"))
                   [Pvar "v2"; Pvar "v1"],
                ECon (Some (Short "Some"))
                  [ECon None
                     [EVar (Short "v2");
                     EVar (Short "v1")]])]));
           (Long "List" (Short "last"),
           Recclosure
             {| sev := nsEmpty; sec := nsEmpty |}
             [("last", "x0",
              EMat (EVar (Short "x0"))
                [(Pcon (Some (Short "[]")) [],
                 ERaise
                   (ECon (Some (Short "Bind")) []));
                (Pcon (Some (Short "::"))
                   [Pvar "v2"; Pvar "v1"],
                EIf
                  (EApp Equality
                     [EVar (Short "v1");
                     ECon (Some (Short "[]")) []])
                  (EVar (Short "v2"))
                  (EApp Opapp
                     [EVar (Short "last");
                     EVar (Short "v1")]))])]
             "last");
           (Long "List" (Short "tl"),
           Closure
             {| sev := nsEmpty; sec := nsEmpty |}
             "v3"
             (EMat (EVar (Short "v3"))
                [(Pcon (Some (Short "[]")) [],
                 ECon (Some (Short "[]")) []);
                (Pcon (Some (Short "::"))
                   [Pvar "v2"; Pvar "v1"],
                EVar (Short "v1"))]));
           (Long "List" (Short "hd"),
           Closure
             {| sev := nsEmpty; sec := nsEmpty |}
             "x0"
             (EMat (EVar (Short "x0"))
                [(Pcon (Some (Short "[]")) [],
                 ERaise
                   (ECon (Some (Short "Bind")) []));
                (Pcon (Some (Short "::"))
                   [Pvar "v2"; Pvar "v1"],
                EVar (Short "v2"))]));
           (Long "List" (Short "@"),
           Closure
             {| sev := nsEmpty; sec := nsEmpty |}
             "v1"
             (EFun "v2"
                (EApp ListAppend
                   [EVar (Short "v1");
                   EVar (Short "v2")])));
           (Long "List" (Short "rev"),
           Closure
             {|
             sev := (Short "rev",
                    Recclosure
                      {|
                      sev := nsEmpty;
                      sec := nsEmpty |}
                      [("rev", "v4",
                       EFun "v3"
                         (EMat
                            (EVar (Short "v4"))
                            [(Pcon
                                (Some
                                (Short "[]")) [],
                             EVar (Short "v3"));
                            (Pcon
                               (Some (Short "::"))
                               [Pvar "v2";
                               Pvar "v1"],
                            EApp Opapp
                              [EApp Opapp
                                [
                                EVar
                                (Short "rev");
                                EVar (Short "v1")];
                              ECon
                                (Some
                                (Short "::"))
                                [
                                EVar
                                (Short "v2");
                                EVar (Short "v3")]])]))]
                      "rev") :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EApp Opapp
                [EApp Opapp
                   [EVar (Short "rev");
                   EVar (Short "v1")];
                ECon (Some (Short "[]")) []]));
           (Long "List" (Short "length"),
           Closure
             {|
             sev := (Short "length_aux",
                    Recclosure
                      {|
                      sev := nsEmpty;
                      sec := nsEmpty |}
                      [("length_aux", "v3",
                       EFun "v4"
                         (EMat
                            (EVar (Short "v3"))
                            [(Pcon
                                (Some
                                (Short "[]")) [],
                             EVar (Short "v4"));
                            (Pcon
                               (Some (Short "::"))
                               [Pvar "v2";
                               Pvar "v1"],
                            EApp Opapp
                              [EApp Opapp
                                [
                                EVar
                                (Short
                                "length_aux");
                                EVar (Short "v1")];
                              EApp
                                (Opn Plus)
                                [
                                EVar
                                (Short "v4");
                                ELit (IntLit 1)]])]))]
                      "length_aux") :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EApp Opapp
                [EApp Opapp
                   [EVar (Short "length_aux");
                   EVar (Short "v1")];
                ELit (IntLit 0)]));
           (Long "List" (Short "null"),
           Closure
             {| sev := nsEmpty; sec := nsEmpty |}
             "v3"
             (EMat (EVar (Short "v3"))
                [(Pcon (Some (Short "[]")) [],
                 EApp (Opb Leq)
                   [ELit (IntLit 0);
                   ELit (IntLit 0)]);
                (Pcon (Some (Short "::"))
                   [Pvar "v2"; Pvar "v1"],
                EApp (Opb Lt)
                  [ELit (IntLit 0);
                  ELit (IntLit 0)])]));
           (Long "Option" (Short "compare"),
           Closure
             {|
             sev := [];
             sec := [(Short "None",
                     (0%nat, TypeStamp "None" 0));
                    (Short "None",
                    (0%nat, TypeStamp "None" 0));
                    (Short "Equal",
                    (0%nat, TypeStamp "Equal" 1));
                    (Short "Some",
                    (1%nat, TypeStamp "Some" 0));
                    (Short "Less",
                    (0%nat, TypeStamp "Less" 1));
                    (Short "Some",
                    (1%nat, TypeStamp "Some" 0));
                    (Short "None",
                    (0%nat, TypeStamp "None" 0));
                    (Short "Greater",
                    (0%nat,
                    TypeStamp "Greater" 1));
                    (Short "Some",
                    (1%nat, TypeStamp "Some" 0))] |}
             "v4"
             (EFun "v5"
                (EFun "v6"
                   (EMat (EVar (Short "v5"))
                      [(Pcon
                          (Some (Short "None"))
                          [],
                       EMat (EVar (Short "v6"))
                         [(Pcon
                             (Some (Short "None"))
                             [],
                          ECon
                            (Some (Short "Equal"))
                            []);
                         (Pcon
                            (Some (Short "Some"))
                            [Pvar "v1"],
                         ECon
                           (Some (Short "Less"))
                           [])]);
                      (Pcon (Some (Short "Some"))
                         [Pvar "v3"],
                      EMat (EVar (Short "v6"))
                        [(Pcon
                            (Some (Short "None"))
                            [],
                         ECon
                           (Some
                              (Short "Greater"))
                           []);
                        (Pcon
                           (Some (Short "Some"))
                           [Pvar "v2"],
                        EApp Opapp
                          [EApp Opapp
                             [EVar (Short "v4");
                             EVar (Short "v3")];
                          EVar (Short "v2")])])]))));
           (Long "Option" (Short "map2"),
           Closure
             {|
             sev := [(Short "isSome",
                     Closure
                       {|
                       sev := [];
                       sec := [(Short "None",
                               (0%nat,
                               TypeStamp "None" 0));
                              (Short "Some",
                              (1%nat,
                              TypeStamp "Some" 0))] |}
                       "v2"
                       (EMat (EVar (Short "v2"))
                          [(Pcon
                              (Some
                                (Short "None"))
                              [],
                           EApp (Opb Lt)
                             [ELit (IntLit 0);
                             ELit (IntLit 0)]);
                          (Pcon
                             (Some (Short "Some"))
                             [Pvar "v1"],
                          EApp (Opb Leq)
                            [ELit (IntLit 0);
                            ELit (IntLit 0)])]));
                    (Short "isSome",
                    Closure
                      {|
                      sev := [];
                      sec := [(Short "None",
                              (0%nat,
                              TypeStamp "None" 0));
                             (Short "Some",
                             (1%nat,
                             TypeStamp "Some" 0))] |}
                      "v2"
                      (EMat (EVar (Short "v2"))
                         [(Pcon
                             (Some (Short "None"))
                             [],
                          EApp (Opb Lt)
                            [ELit (IntLit 0);
                            ELit (IntLit 0)]);
                         (Pcon
                            (Some (Short "Some"))
                            [Pvar "v1"],
                         EApp (Opb Leq)
                           [ELit (IntLit 0);
                           ELit (IntLit 0)])]));
                    (Short "valOf",
                    Closure
                      {|
                      sev := [];
                      sec := [(Short "None",
                              (0%nat,
                              TypeStamp "None" 0));
                             (Short "Some",
                             (1%nat,
                             TypeStamp "Some" 0))] |}
                      "x0"
                      (EMat (EVar (Short "x0"))
                         [(Pcon
                             (Some (Short "None"))
                             [],
                          ERaise
                            (ECon
                               (Some
                                (Short "Bind"))
                               []));
                         (Pcon
                            (Some (Short "Some"))
                            [Pvar "v1"],
                         EVar (Short "v1"))]));
                    (Short "valOf",
                    Closure
                      {|
                      sev := [];
                      sec := [(Short "None",
                              (0%nat,
                              TypeStamp "None" 0));
                             (Short "Some",
                             (1%nat,
                             TypeStamp "Some" 0))] |}
                      "x0"
                      (EMat (EVar (Short "x0"))
                         [(Pcon
                             (Some (Short "None"))
                             [],
                          ERaise
                            (ECon
                               (Some
                                (Short "Bind"))
                               []));
                         (Pcon
                            (Some (Short "Some"))
                            [Pvar "v1"],
                         EVar (Short "v1"))]))];
             sec := [(Short "Some",
                     (1%nat, TypeStamp "Some" 0));
                    (Short "None",
                    (0%nat, TypeStamp "None" 0))] |}
             "v1"
             (EFun "v2"
                (EFun "v3"
                   (EIf
                      (ELog And
                         (EApp Opapp
                            [EVar
                               (Short "isSome");
                            EVar (Short "v2")])
                         (EApp Opapp
                            [EVar
                               (Short "isSome");
                            EVar (Short "v3")]))
                      (ECon (Some (Short "Some"))
                         [EApp Opapp
                            [EApp Opapp
                               [EVar (Short "v1");
                               EApp Opapp
                                [
                                EVar
                                (Short "valOf");
                                EVar (Short "v2")]];
                            EApp Opapp
                              [EVar
                                (Short "valOf");
                              EVar (Short "v3")]]])
                      (ECon (Some (Short "None"))
                         [])))));
           (Long "Option" (Short "isNone"),
           Closure
             {|
             sev := [];
             sec := [(Short "None",
                     (0%nat, TypeStamp "None" 0));
                    (Short "Some",
                    (1%nat, TypeStamp "Some" 0))] |}
             "v2"
             (EMat (EVar (Short "v2"))
                [(Pcon (Some (Short "None")) [],
                 EApp (Opb Leq)
                   [ELit (IntLit 0);
                   ELit (IntLit 0)]);
                (Pcon (Some (Short "Some"))
                   [Pvar "v1"],
                EApp (Opb Lt)
                  [ELit (IntLit 0);
                  ELit (IntLit 0)])]));
           (Long "Option"
              (Short "composePartial"),
           Closure
             {|
             sev := [];
             sec := [(Short "None",
                     (0%nat, TypeStamp "None" 0));
                    (Short "None",
                    (0%nat, TypeStamp "None" 0));
                    (Short "Some",
                    (1%nat, TypeStamp "Some" 0))] |}
             "v3"
             (EFun "v4"
                (EFun "v2"
                   (EMat
                      (EApp Opapp
                         [EVar (Short "v4");
                         EVar (Short "v2")])
                      [(Pcon
                          (Some (Short "None"))
                          [],
                       ECon (Some (Short "None"))
                         []);
                      (Pcon (Some (Short "Some"))
                         [Pvar "v1"],
                      EApp Opapp
                        [EVar (Short "v3");
                        EVar (Short "v1")])]))));
           (Long "Option" (Short "compose"),
           Closure
             {|
             sev := [];
             sec := [(Short "None",
                     (0%nat, TypeStamp "None" 0));
                    (Short "None",
                    (0%nat, TypeStamp "None" 0));
                    (Short "Some",
                    (1%nat, TypeStamp "Some" 0));
                    (Short "Some",
                    (1%nat, TypeStamp "Some" 0))] |}
             "v3"
             (EFun "v4"
                (EFun "v2"
                   (EMat
                      (EApp Opapp
                         [EVar (Short "v4");
                         EVar (Short "v2")])
                      [(Pcon
                          (Some (Short "None"))
                          [],
                       ECon (Some (Short "None"))
                         []);
                      (Pcon (Some (Short "Some"))
                         [Pvar "v1"],
                      ECon (Some (Short "Some"))
                        [EApp Opapp
                           [EVar (Short "v3");
                           EVar (Short "v1")]])]))));
           (Long "Option" (Short "mapPartial"),
           Closure
             {|
             sev := [];
             sec := [(Short "None",
                     (0%nat, TypeStamp "None" 0));
                    (Short "None",
                    (0%nat, TypeStamp "None" 0));
                    (Short "Some",
                    (1%nat, TypeStamp "Some" 0))] |}
             "v2"
             (EFun "v3"
                (EMat (EVar (Short "v3"))
                   [(Pcon (Some (Short "None"))
                       [],
                    ECon (Some (Short "None")) []);
                   (Pcon (Some (Short "Some"))
                      [Pvar "v1"],
                   EApp Opapp
                     [EVar (Short "v2");
                     EVar (Short "v1")])])));
           (Long "Option" (Short "map"),
           Closure
             {|
             sev := [];
             sec := [(Short "None",
                     (0%nat, TypeStamp "None" 0));
                    (Short "None",
                    (0%nat, TypeStamp "None" 0));
                    (Short "Some",
                    (1%nat, TypeStamp "Some" 0));
                    (Short "Some",
                    (1%nat, TypeStamp "Some" 0))] |}
             "v2"
             (EFun "v3"
                (EMat (EVar (Short "v3"))
                   [(Pcon (Some (Short "None"))
                       [],
                    ECon (Some (Short "None")) []);
                   (Pcon (Some (Short "Some"))
                      [Pvar "v1"],
                   ECon (Some (Short "Some"))
                     [EApp Opapp
                        [EVar (Short "v2");
                        EVar (Short "v1")]])])));
           (Long "Option" (Short "join"),
           Closure
             {|
             sev := [];
             sec := [(Short "None",
                     (0%nat, TypeStamp "None" 0));
                    (Short "None",
                    (0%nat, TypeStamp "None" 0));
                    (Short "Some",
                    (1%nat, TypeStamp "Some" 0))] |}
             "v2"
             (EMat (EVar (Short "v2"))
                [(Pcon (Some (Short "None")) [],
                 ECon (Some (Short "None")) []);
                (Pcon (Some (Short "Some"))
                   [Pvar "v1"],
                EVar (Short "v1"))]));
           (Long "Option" (Short "valOf"),
           Closure
             {|
             sev := [];
             sec := [(Short "None",
                     (0%nat, TypeStamp "None" 0));
                    (Short "Some",
                    (1%nat, TypeStamp "Some" 0))] |}
             "x0"
             (EMat (EVar (Short "x0"))
                [(Pcon (Some (Short "None")) [],
                 ERaise
                   (ECon (Some (Short "Bind")) []));
                (Pcon (Some (Short "Some"))
                   [Pvar "v1"],
                EVar (Short "v1"))]));
           (Long "Option" (Short "isSome"),
           Closure
             {|
             sev := [];
             sec := [(Short "None",
                     (0%nat, TypeStamp "None" 0));
                    (Short "Some",
                    (1%nat, TypeStamp "Some" 0))] |}
             "v2"
             (EMat (EVar (Short "v2"))
                [(Pcon (Some (Short "None")) [],
                 EApp (Opb Lt)
                   [ELit (IntLit 0);
                   ELit (IntLit 0)]);
                (Pcon (Some (Short "Some"))
                   [Pvar "v1"],
                EApp (Opb Leq)
                  [ELit (IntLit 0);
                  ELit (IntLit 0)])]));
           (Long "Option" (Short "getOpt"),
           Closure
             {|
             sev := [];
             sec := [(Short "None",
                     (0%nat, TypeStamp "None" 0));
                    (Short "Some",
                    (1%nat, TypeStamp "Some" 0))] |}
             "v3"
             (EFun "v2"
                (EMat (EVar (Short "v3"))
                   [(Pcon (Some (Short "None"))
                       [], EVar (Short "v2"));
                   (Pcon (Some (Short "Some"))
                      [Pvar "v1"],
                   EVar (Short "v1"))])));
           (Long "Runtime" (Short "abort"),
           Recclosure
             {|
             sev := [(Short "exit",
                     Recclosure
                       {| sev := []; sec := [] |}
                       [("exit", "i",
                        ELet (Some "y")
                          (EApp (WordFromInt W8)
                             [EVar (Short "i")])
                          (ELet (Some "x")
                             (EApp Aw8alloc
                                [
                                ELit (IntLit 1);
                                EVar (Short "y")])
                             (EApp
                                (FFI "exit")
                                [
                                ELit (StrLit "");
                                EVar (Short "x")])))]
                       "exit")];
             sec := [] |}
             [("abort", "u",
              EMat (EVar (Short "u"))
                [(Pcon None [],
                 EApp Opapp
                   [EVar (Short "exit");
                   ELit (IntLit 1)])])] "abort");
           (Long "Runtime" (Short "exit"),
           Recclosure {| sev := []; sec := [] |}
             [("exit", "i",
              ELet (Some "y")
                (EApp (WordFromInt W8)
                   [EVar (Short "i")])
                (ELet (Some "x")
                   (EApp Aw8alloc
                      [ELit (IntLit 1);
                      EVar (Short "y")])
                   (EApp (FFI "exit")
                      [ELit (StrLit "");
                      EVar (Short "x")])))]
             "exit");
           (Long "Runtime" (Short "debugMsg"),
           Closure {| sev := []; sec := [] |}
             "v1"
             (EApp (FFI "")
                [EVar (Short "v1");
                EApp Aw8alloc
                  [ELit (IntLit 0);
                  ELit
                    (Word8Lit (nat_to_word 8 0))]]));
           (Long "Runtime" (Short "fail"),
           Closure {| sev := []; sec := [] |}
             "v1"
             (EMat (EVar (Short "v1"))
                [(Pcon None [],
                 ELet (Some "a")
                   (EVar (Short "v1"))
                   (ELet (Some "n")
                      (ELit
                         (StrLit
                            "18446744073709551616"))
                      (ELet None
                         (EApp Aalloc
                            [EVar (Short "n");
                            EVar (Short "n")])
                         (EVar (Short "a")))))]));
           (Long "Runtime" (Short "fullGC"),
           Closure {| sev := []; sec := [] |}
             "v1"
             (EMat (EVar (Short "v1"))
                [(Pcon None [],
                 EApp ConfigGC
                   [ELit (IntLit 0);
                   ELit (IntLit 0)])]));
           (Short "repeat",
           Recclosure {| sev := []; sec := [] |}
             [("repeat", "f",
              EFun "x"
                (ELet (Some "a")
                   (EApp Opapp
                      [EVar (Short "f");
                      EVar (Short "x")])
                   (EApp Opapp
                      [EApp Opapp
                         [EVar (Short "repeat");
                         EVar (Short "f")];
                      EVar (Short "a")])))]
             "repeat");
           (Short "least",
           Closure
             {|
             sev := [(Short "while",
                     Recclosure
                       {| sev := []; sec := [] |}
                       [("while", "v1",
                        EFun "v2"
                          (EFun "v3"
                             (EIf
                                (EApp Opapp
                                [
                                EVar
                                (Short "v1");
                                EVar (Short "v3")])
                                (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "while");
                                EVar (Short "v1")];
                                EVar (Short "v2")];
                                EApp Opapp
                                [
                                EVar
                                (Short "v2");
                                EVar (Short "v3")]])
                                (EVar
                                (Short "v3")))))]
                       "while")];
             sec := [] |} "v3"
             (EApp Opapp
                [EApp Opapp
                   [EApp Opapp
                      [EVar (Short "while");
                      EFun "v1"
                        (EApp Equality
                           [EApp Opapp
                              [EVar (Short "v3");
                              EVar (Short "v1")];
                           EApp (Opb Lt)
                             [ELit (IntLit 0);
                             ELit (IntLit 0)]])];
                   EFun "v2"
                     (EApp (Opn Plus)
                        [EVar (Short "v2");
                        ELit (IntLit 1)])];
                ELit (IntLit 0)]));
           (Short "owhile",
           Recclosure {| sev := []; sec := [] |}
             [("owhile", "v1",
              EFun "v2"
                (EFun "v3"
                   (EIf
                      (EApp Opapp
                         [EVar (Short "v1");
                         EVar (Short "v3")])
                      (EApp Opapp
                         [EApp Opapp
                            [EApp Opapp
                               [EVar
                                (Short "owhile");
                               EVar (Short "v1")];
                            EVar (Short "v2")];
                         EApp Opapp
                           [EVar (Short "v2");
                           EVar (Short "v3")]])
                      (ECon (Some (Short "Some"))
                         [EVar (Short "v3")]))))]
             "owhile");
           (Short "while",
           Recclosure {| sev := []; sec := [] |}
             [("while", "v1",
              EFun "v2"
                (EFun "v3"
                   (EIf
                      (EApp Opapp
                         [EVar (Short "v1");
                         EVar (Short "v3")])
                      (EApp Opapp
                         [EApp Opapp
                            [EApp Opapp
                               [EVar
                                (Short "while");
                               EVar (Short "v1")];
                            EVar (Short "v2")];
                         EApp Opapp
                           [EVar (Short "v2");
                           EVar (Short "v3")]])
                      (EVar (Short "v3")))))]
             "while");
           (Short "pre",
           Closure {| sev := []; sec := [] |}
             "v1"
             (ELet (Some "k")
                (EApp (Opn Minus)
                   [EVar (Short "v1");
                   ELit (IntLit 1)])
                (EIf
                   (EApp (Opb Lt)
                      [EVar (Short "k");
                      ELit (IntLit 0)])
                   (ELit (IntLit 0))
                   (EVar (Short "k")))));
           (Short "abs_diff",
           Closure {| sev := []; sec := [] |}
             "v2"
             (EFun "v1"
                (EIf
                   (EApp (Opb Lt)
                      [EVar (Short "v2");
                      EVar (Short "v1")])
                   (ELet (Some "k")
                      (EApp (Opn Minus)
                         [EVar (Short "v1");
                         EVar (Short "v2")])
                      (EIf
                         (EApp (Opb Lt)
                            [EVar (Short "k");
                            ELit (IntLit 0)])
                         (ELit (IntLit 0))
                         (EVar (Short "k"))))
                   (ELet (Some "k")
                      (EApp (Opn Minus)
                         [EVar (Short "v2");
                         EVar (Short "v1")])
                      (EIf
                         (EApp (Opb Lt)
                            [EVar (Short "k");
                            ELit (IntLit 0)])
                         (ELit (IntLit 0))
                         (EVar (Short "k")))))));
           (Short "funpow",
           Recclosure {| sev := []; sec := [] |}
             [("funpow", "v1",
              EFun "v2"
                (EFun "v3"
                   (EIf
                      (EApp Equality
                         [EVar (Short "v2");
                         ELit (IntLit 0)])
                      (EVar (Short "v3"))
                      (EApp Opapp
                         [EApp Opapp
                            [EApp Opapp
                               [EVar
                                (Short "funpow");
                               EVar (Short "v1")];
                            ELet
                              (Some "k")
                              (EApp
                                (Opn Minus)
                                [
                                EVar
                                (Short "v2");
                                ELit (IntLit 1)])
                              (EIf
                                (EApp
                                (Opb Lt)
                                [
                                EVar (Short "k");
                                ELit (IntLit 0)])
                                (ELit (IntLit 0))
                                (EVar (Short "k")))];
                         EApp Opapp
                           [EVar (Short "v1");
                           EVar (Short "v3")]]))))]
             "funpow");
           (Short "odd",
           Closure {| sev := []; sec := [] |}
             "v1"
             (EApp (Opb Lt)
                [ELit (IntLit 0);
                EApp (Opn Modulo)
                  [EVar (Short "v1");
                  ELit (IntLit 2)]]));
           (Short "even",
           Closure {| sev := []; sec := [] |}
             "v1"
             (EApp Equality
                [EApp (Opn Modulo)
                   [EVar (Short "v1");
                   ELit (IntLit 2)];
                ELit (IntLit 0)]));
           (Short "max",
           Closure {| sev := []; sec := [] |}
             "v1"
             (EFun "v2"
                (EIf
                   (EApp (Opb Lt)
                      [EVar (Short "v1");
                      EVar (Short "v2")])
                   (EVar (Short "v2"))
                   (EVar (Short "v1")))));
           (Short "min",
           Closure {| sev := []; sec := [] |}
             "v1"
             (EFun "v2"
                (EIf
                   (EApp (Opb Lt)
                      [EVar (Short "v1");
                      EVar (Short "v2")])
                   (EVar (Short "v1"))
                   (EVar (Short "v2")))));
           (Short "exp",
           Closure
             {|
             sev := [(Short "exp",
                     Recclosure
                       {| sev := []; sec := [] |}
                       [("exp", "v2",
                        EFun "v3"
                          (EFun "v1"
                             (EIf
                                (EApp Equality
                                [
                                EVar
                                (Short "v3");
                                ELit (IntLit 0)])
                                (EVar
                                (Short "v1"))
                                (EApp Opapp
                                [
                                EApp Opapp
                                [
                                EApp Opapp
                                [
                                EVar
                                (Short "exp");
                                EVar (Short "v2")];
                                ELet
                                (Some "k")
                                (EApp
                                (Opn Minus)
                                [
                                EVar
                                (Short "v3");
                                ELit (IntLit 1)])
                                (EIf
                                (EApp
                                (Opb Lt)
                                [
                                EVar (Short "k");
                                ELit (IntLit 0)])
                                (ELit (IntLit 0))
                                (EVar (Short "k")))];
                                EApp
                                (Opn Times)
                                [
                                EVar
                                (Short "v2");
                                EVar (Short "v1")]]))))]
                       "exp")];
             sec := [] |} "v1"
             (EFun "v2"
                (EApp Opapp
                   [EApp Opapp
                      [EApp Opapp
                         [EVar (Short "exp");
                         EVar (Short "v1")];
                      EVar (Short "v2")];
                   ELit (IntLit 1)])));
           (Short "exp",
           Recclosure {| sev := []; sec := [] |}
             [("exp", "v2",
              EFun "v3"
                (EFun "v1"
                   (EIf
                      (EApp Equality
                         [EVar (Short "v3");
                         ELit (IntLit 0)])
                      (EVar (Short "v1"))
                      (EApp Opapp
                         [EApp Opapp
                            [EApp Opapp
                               [EVar
                                (Short "exp");
                               EVar (Short "v2")];
                            ELet
                              (Some "k")
                              (EApp
                                (Opn Minus)
                                [
                                EVar
                                (Short "v3");
                                ELit (IntLit 1)])
                              (EIf
                                (EApp
                                (Opb Lt)
                                [
                                EVar (Short "k");
                                ELit (IntLit 0)])
                                (ELit (IntLit 0))
                                (EVar (Short "k")))];
                         EApp (Opn Times)
                           [EVar (Short "v2");
                           EVar (Short "v1")]]))))]
             "exp");
           (Short "update",
           Closure {| sev := []; sec := [] |}
             "v3"
             (EFun "v4"
                (EFun "v2"
                   (EFun "v1"
                      (EIf
                         (EApp Equality
                            [EVar (Short "v3");
                            EVar (Short "v1")])
                         (EVar (Short "v4"))
                         (EApp Opapp
                            [EVar (Short "v2");
                            EVar (Short "v1")]))))));
           (Short "const",
           Closure {| sev := []; sec := [] |}
             "v2" (EFun "v1" (EVar (Short "v2"))));
           (Short "flip",
           Closure {| sev := []; sec := [] |}
             "v3"
             (EFun "v2"
                (EFun "v1"
                   (EApp Opapp
                      [EApp Opapp
                         [EVar (Short "v3");
                         EVar (Short "v1")];
                      EVar (Short "v2")]))));
           (Short "id",
           Closure {| sev := []; sec := [] |}
             "v1" (EVar (Short "v1")));
           (Short "o",
           Closure {| sev := []; sec := [] |}
             "v2"
             (EFun "v3"
                (EFun "v1"
                   (EApp Opapp
                      [EVar (Short "v2");
                      EApp Opapp
                        [EVar (Short "v3");
                        EVar (Short "v1")]]))));
           (Short "uncurry",
           Closure
             {|
             sev := [(Short "fst",
                     Closure
                       {| sev := []; sec := [] |}
                       "v3"
                       (EMat (EVar (Short "v3"))
                          [(Pcon None
                              [Pvar "v2";
                              Pvar "v1"],
                           EVar (Short "v2"))]));
                    (Short "snd",
                    Closure
                      {| sev := []; sec := [] |}
                      "v3"
                      (EMat (EVar (Short "v3"))
                         [(Pcon None
                             [Pvar "v2";
                             Pvar "v1"],
                          EVar (Short "v1"))]))];
             sec := [] |} "v1"
             (EFun "v2"
                (EApp Opapp
                   [EApp Opapp
                      [EVar (Short "v1");
                      EApp Opapp
                        [EVar (Short "fst");
                        EVar (Short "v2")]];
                   EApp Opapp
                     [EVar (Short "snd");
                     EVar (Short "v2")]])));
           (Short "curry",
           Closure {| sev := []; sec := [] |}
             "v1"
             (EFun "v2"
                (EFun "v3"
                   (EApp Opapp
                      [EVar (Short "v1");
                      ECon None
                        [EVar (Short "v2");
                        EVar (Short "v3")]]))));
           (Short "snd",
           Closure {| sev := []; sec := [] |}
             "v3"
             (EMat (EVar (Short "v3"))
                [(Pcon None
                    [Pvar "v2"; Pvar "v1"],
                 EVar (Short "v1"))]));
           (Short "fst",
           Closure {| sev := []; sec := [] |}
             "v3"
             (EMat (EVar (Short "v3"))
                [(Pcon None
                    [Pvar "v2"; Pvar "v1"],
                 EVar (Short "v2"))]))];
    sec := [(Short "Inl",
            (1%nat, TypeStamp "Inl" 2));
           (Short "Inr",
           (1%nat, TypeStamp "Inr" 2));
           (Short "Less",
           (0%nat, TypeStamp "Less" 1));
           (Short "Equal",
           (0%nat, TypeStamp "Equal" 1));
           (Short "Greater",
           (0%nat, TypeStamp "Greater" 1));
           (Short "None",
           (0%nat, TypeStamp "None" 0));
           (Short "Some",
           (1%nat, TypeStamp "Some" 0))] |}.

Definition env_28_29 := {|
    sev := [(Long "Vector" (Short "collate"),
            Closure
              {|
              sev := (Short "collate_aux",
                     Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                       [("collate_aux", "v1",
                        EFun "v5"
                          (EFun "v6"
                             (EFun "v2"
                                (EFun "v3"
                                   (EFun "v4"
                                      (EIf (EApp Equality [EVar (Short "v4"); ELit (IntLit 0)])
                                         (EVar (Short "v3"))
                                         (EIf
                                            (EApp Equality
                                               [EApp Opapp
                                                  [EApp Opapp
                                                     [EVar (Short "v1");
                                                     EApp Vsub [EVar (Short "v5"); EVar (Short "v2")]];
                                                  EApp Vsub [EVar (Short "v6"); EVar (Short "v2")]];
                                               ECon (Some (Short "Equal")) []])
                                            (EApp Opapp
                                               [EApp Opapp
                                                  [EApp Opapp
                                                     [EApp Opapp
                                                        [EApp Opapp
                                                           [EApp Opapp
                                                              [EVar (Short "collate_aux");
                                                              EVar (Short "v1")];
                                                           EVar (Short "v5")];
                                                        EVar (Short "v6")];
                                                     EApp (Opn Plus)
                                                       [EVar (Short "v2"); ELit (IntLit 1)]];
                                                  EVar (Short "v3")];
                                               ELet (Some "k")
                                                 (EApp (Opn Minus) [EVar (Short "v4"); ELit (IntLit 1)])
                                                 (EIf
                                                    (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                                    (ELit (IntLit 0)) (EVar (Short "k")))])
                                            (EApp Opapp
                                               [EApp Opapp
                                                  [EVar (Short "v1");
                                                  EApp Vsub [EVar (Short "v5"); EVar (Short "v2")]];
                                               EApp Vsub [EVar (Short "v6"); EVar (Short "v2")]]))))))))]
                       "collate_aux")
                     :: (Short "collate_aux",
                        Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                          [("collate_aux", "v1",
                           EFun "v5"
                             (EFun "v6"
                                (EFun "v2"
                                   (EFun "v3"
                                      (EFun "v4"
                                         (EIf (EApp Equality [EVar (Short "v4"); ELit (IntLit 0)])
                                            (EVar (Short "v3"))
                                            (EIf
                                               (EApp Equality
                                                  [EApp Opapp
                                                     [EApp Opapp
                                                        [EVar (Short "v1");
                                                        EApp Vsub
                                                          [EVar (Short "v5"); EVar (Short "v2")]];
                                                     EApp Vsub [EVar (Short "v6"); EVar (Short "v2")]];
                                                  ECon (Some (Short "Equal")) []])
                                               (EApp Opapp
                                                  [EApp Opapp
                                                     [EApp Opapp
                                                        [EApp Opapp
                                                           [EApp Opapp
                                                              [EApp Opapp
                                                                 [EVar (Short "collate_aux");
                                                                 EVar (Short "v1")];
                                                              EVar (Short "v5")];
                                                           EVar (Short "v6")];
                                                        EApp (Opn Plus)
                                                          [EVar (Short "v2"); ELit (IntLit 1)]];
                                                     EVar (Short "v3")];
                                                  ELet (Some "k")
                                                    (EApp (Opn Minus)
                                                       [EVar (Short "v4"); ELit (IntLit 1)])
                                                    (EIf
                                                       (EApp (Opb Lt)
                                                          [EVar (Short "k"); ELit (IntLit 0)])
                                                       (ELit (IntLit 0)) (EVar (Short "k")))])
                                               (EApp Opapp
                                                  [EApp Opapp
                                                     [EVar (Short "v1");
                                                     EApp Vsub [EVar (Short "v5"); EVar (Short "v2")]];
                                                  EApp Vsub [EVar (Short "v6"); EVar (Short "v2")]]))))))))]
                          "collate_aux")
                        :: (Short "collate_aux",
                           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                             [("collate_aux", "v1",
                              EFun "v5"
                                (EFun "v6"
                                   (EFun "v2"
                                      (EFun "v3"
                                         (EFun "v4"
                                            (EIf (EApp Equality [EVar (Short "v4"); ELit (IntLit 0)])
                                               (EVar (Short "v3"))
                                               (EIf
                                                  (EApp Equality
                                                     [EApp Opapp
                                                        [EApp Opapp
                                                           [EVar (Short "v1");
                                                           EApp Vsub
                                                             [EVar (Short "v5"); EVar (Short "v2")]];
                                                        EApp Vsub
                                                          [EVar (Short "v6"); EVar (Short "v2")]];
                                                     ECon (Some (Short "Equal")) []])
                                                  (EApp Opapp
                                                     [EApp Opapp
                                                        [EApp Opapp
                                                           [EApp Opapp
                                                              [EApp Opapp
                                                                 [EApp Opapp
                                                                    [EVar (Short "collate_aux");
                                                                    EVar (Short "v1")];
                                                                 EVar (Short "v5")];
                                                              EVar (Short "v6")];
                                                           EApp (Opn Plus)
                                                             [EVar (Short "v2"); ELit (IntLit 1)]];
                                                        EVar (Short "v3")];
                                                     ELet (Some "k")
                                                       (EApp (Opn Minus)
                                                          [EVar (Short "v4"); ELit (IntLit 1)])
                                                       (EIf
                                                          (EApp (Opb Lt)
                                                             [EVar (Short "k"); ELit (IntLit 0)])
                                                          (ELit (IntLit 0))
                                                          (EVar (Short "k")))])
                                                  (EApp Opapp
                                                     [EApp Opapp
                                                        [EVar (Short "v1");
                                                        EApp Vsub
                                                          [EVar (Short "v5"); EVar (Short "v2")]];
                                                     EApp Vsub [EVar (Short "v6"); EVar (Short "v2")]]))))))))]
                             "collate_aux") :: nsEmpty;
              sec := (Short "Less", (0%nat, TypeStamp "Less" 1))
                     :: (Short "Greater", (0%nat, TypeStamp "Greater" 1))
                        :: (Short "Equal", (0%nat, TypeStamp "Equal" 1)) :: nsEmpty |} "v1"
              (EFun "v2"
                 (EFun "v3"
                    (EIf
                       (EApp (Opb Lt)
                          [EApp Vlength [EVar (Short "v2")]; EApp Vlength [EVar (Short "v3")]])
                       (EApp Opapp
                          [EApp Opapp
                             [EApp Opapp
                                [EApp Opapp
                                   [EApp Opapp
                                      [EApp Opapp [EVar (Short "collate_aux"); EVar (Short "v1")];
                                      EVar (Short "v2")]; EVar (Short "v3")];
                                ELit (IntLit 0)]; ECon (Some (Short "Less")) []];
                          EApp Vlength [EVar (Short "v2")]])
                       (EIf
                          (EApp (Opb Lt)
                             [EApp Vlength [EVar (Short "v3")]; EApp Vlength [EVar (Short "v2")]])
                          (EApp Opapp
                             [EApp Opapp
                                [EApp Opapp
                                   [EApp Opapp
                                      [EApp Opapp
                                         [EApp Opapp [EVar (Short "collate_aux"); EVar (Short "v1")];
                                         EVar (Short "v2")]; EVar (Short "v3")];
                                   ELit (IntLit 0)]; ECon (Some (Short "Greater")) []];
                             EApp Vlength [EVar (Short "v3")]])
                          (EApp Opapp
                             [EApp Opapp
                                [EApp Opapp
                                   [EApp Opapp
                                      [EApp Opapp
                                         [EApp Opapp [EVar (Short "collate_aux"); EVar (Short "v1")];
                                         EVar (Short "v2")]; EVar (Short "v3")];
                                   ELit (IntLit 0)]; ECon (Some (Short "Equal")) []];
                             EApp Vlength [EVar (Short "v3")]]))))));
           (Long "Vector" (Short "all"),
           Closure
             {|
             sev := (Short "all_aux",
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("all_aux", "v1",
                       EFun "v4"
                         (EFun "v2"
                            (EFun "v3"
                               (EIf (EApp Equality [EVar (Short "v3"); ELit (IntLit 0)])
                                  (EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)])
                                  (EIf
                                     (EApp Opapp
                                        [EVar (Short "v1");
                                        EApp Vsub [EVar (Short "v4"); EVar (Short "v2")]])
                                     (EApp Opapp
                                        [EApp Opapp
                                           [EApp Opapp
                                              [EApp Opapp [EVar (Short "all_aux"); EVar (Short "v1")];
                                              EVar (Short "v4")];
                                           EApp (Opn Plus) [EVar (Short "v2"); ELit (IntLit 1)]];
                                        ELet (Some "k")
                                          (EApp (Opn Minus) [EVar (Short "v3"); ELit (IntLit 1)])
                                          (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                             (ELit (IntLit 0)) (EVar (Short "k")))])
                                     (EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]))))))] "all_aux")
                    :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EFun "v2"
                (EApp Opapp
                   [EApp Opapp
                      [EApp Opapp
                         [EApp Opapp [EVar (Short "all_aux"); EVar (Short "v1")]; EVar (Short "v2")];
                      ELit (IntLit 0)]; EApp Vlength [EVar (Short "v2")]])));
           (Long "Vector" (Short "exists"),
           Closure
             {|
             sev := (Short "exists_aux",
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("exists_aux", "v1",
                       EFun "v4"
                         (EFun "v2"
                            (EFun "v3"
                               (EIf (EApp Equality [EVar (Short "v3"); ELit (IntLit 0)])
                                  (EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)])
                                  (EIf
                                     (EApp Opapp
                                        [EVar (Short "v1");
                                        EApp Vsub [EVar (Short "v4"); EVar (Short "v2")]])
                                     (EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)])
                                     (EApp Opapp
                                        [EApp Opapp
                                           [EApp Opapp
                                              [EApp Opapp
                                                 [EVar (Short "exists_aux"); EVar (Short "v1")];
                                              EVar (Short "v4")];
                                           EApp (Opn Plus) [EVar (Short "v2"); ELit (IntLit 1)]];
                                        ELet (Some "k")
                                          (EApp (Opn Minus) [EVar (Short "v3"); ELit (IntLit 1)])
                                          (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                             (ELit (IntLit 0)) (EVar (Short "k")))]))))))] "exists_aux")
                    :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EFun "v2"
                (EApp Opapp
                   [EApp Opapp
                      [EApp Opapp
                         [EApp Opapp [EVar (Short "exists_aux"); EVar (Short "v1")]; EVar (Short "v2")];
                      ELit (IntLit 0)]; EApp Vlength [EVar (Short "v2")]])));
           (Long "Vector" (Short "find"),
           Closure
             {|
             sev := (Short "find_aux",
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("find_aux", "v1",
                       EFun "v4"
                         (EFun "v2"
                            (EFun "v3"
                               (EIf (EApp Equality [EVar (Short "v3"); ELit (IntLit 0)])
                                  (ECon (Some (Short "None")) [])
                                  (EIf
                                     (EApp Opapp
                                        [EVar (Short "v1");
                                        EApp Vsub [EVar (Short "v4"); EVar (Short "v2")]])
                                     (ECon (Some (Short "Some"))
                                        [EApp Vsub [EVar (Short "v4"); EVar (Short "v2")]])
                                     (EApp Opapp
                                        [EApp Opapp
                                           [EApp Opapp
                                              [EApp Opapp [EVar (Short "find_aux"); EVar (Short "v1")];
                                              EVar (Short "v4")];
                                           EApp (Opn Plus) [EVar (Short "v2"); ELit (IntLit 1)]];
                                        ELet (Some "k")
                                          (EApp (Opn Minus) [EVar (Short "v3"); ELit (IntLit 1)])
                                          (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                             (ELit (IntLit 0)) (EVar (Short "k")))]))))))] "find_aux")
                    :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EFun "v2"
                (EApp Opapp
                   [EApp Opapp
                      [EApp Opapp
                         [EApp Opapp [EVar (Short "find_aux"); EVar (Short "v1")]; EVar (Short "v2")];
                      ELit (IntLit 0)]; EApp Vlength [EVar (Short "v2")]])));
           (Long "Vector" (Short "findi"),
           Closure
             {|
             sev := (Short "findi_aux",
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("findi_aux", "v1",
                       EFun "v4"
                         (EFun "v2"
                            (EFun "v3"
                               (EIf (EApp Equality [EVar (Short "v3"); ELit (IntLit 0)])
                                  (ECon (Some (Short "None")) [])
                                  (EIf
                                     (EApp Opapp
                                        [EApp Opapp [EVar (Short "v1"); EVar (Short "v2")];
                                        EApp Vsub [EVar (Short "v4"); EVar (Short "v2")]])
                                     (ECon (Some (Short "Some"))
                                        [ECon None
                                           [EVar (Short "v2");
                                           EApp Vsub [EVar (Short "v4"); EVar (Short "v2")]]])
                                     (EApp Opapp
                                        [EApp Opapp
                                           [EApp Opapp
                                              [EApp Opapp [EVar (Short "findi_aux"); EVar (Short "v1")];
                                              EVar (Short "v4")];
                                           EApp (Opn Plus) [EVar (Short "v2"); ELit (IntLit 1)]];
                                        ELet (Some "k")
                                          (EApp (Opn Minus) [EVar (Short "v3"); ELit (IntLit 1)])
                                          (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                             (ELit (IntLit 0)) (EVar (Short "k")))]))))))] "findi_aux")
                    :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EFun "v2"
                (EApp Opapp
                   [EApp Opapp
                      [EApp Opapp
                         [EApp Opapp [EVar (Short "findi_aux"); EVar (Short "v1")]; EVar (Short "v2")];
                      ELit (IntLit 0)]; EApp Vlength [EVar (Short "v2")]])));
           (Long "Vector" (Short "foldr"),
           Closure
             {|
             sev := (Short "foldr_aux",
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("foldr_aux", "v2",
                       EFun "v1"
                         (EFun "v4"
                            (EFun "v3"
                               (EIf (EApp Equality [EVar (Short "v3"); ELit (IntLit 0)])
                                  (EVar (Short "v1"))
                                  (EApp Opapp
                                     [EApp Opapp
                                        [EApp Opapp
                                           [EApp Opapp [EVar (Short "foldr_aux"); EVar (Short "v2")];
                                           EApp Opapp
                                             [EApp Opapp
                                                [EVar (Short "v2");
                                                EApp Vsub
                                                  [EVar (Short "v4");
                                                  ELet (Some "k")
                                                    (EApp (Opn Minus)
                                                       [EVar (Short "v3"); ELit (IntLit 1)])
                                                    (EIf
                                                       (EApp (Opb Lt)
                                                          [EVar (Short "k"); ELit (IntLit 0)])
                                                       (ELit (IntLit 0)) (EVar (Short "k")))]];
                                             EVar (Short "v1")]]; EVar (Short "v4")];
                                     ELet (Some "k")
                                       (EApp (Opn Minus) [EVar (Short "v3"); ELit (IntLit 1)])
                                       (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                          (ELit (IntLit 0)) (EVar (Short "k")))])))))] "foldr_aux")
                    :: nsEmpty;
             sec := nsEmpty |} "v2"
             (EFun "v1"
                (EFun "v3"
                   (EApp Opapp
                      [EApp Opapp
                         [EApp Opapp
                            [EApp Opapp [EVar (Short "foldr_aux"); EVar (Short "v2")];
                            EVar (Short "v1")]; EVar (Short "v3")]; EApp Vlength [EVar (Short "v3")]]))));
           (Long "Vector" (Short "foldri"),
           Closure
             {|
             sev := (Short "foldri_aux",
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("foldri_aux", "v2",
                       EFun "v1"
                         (EFun "v4"
                            (EFun "v3"
                               (EIf (EApp Equality [EVar (Short "v3"); ELit (IntLit 0)])
                                  (EVar (Short "v1"))
                                  (EApp Opapp
                                     [EApp Opapp
                                        [EApp Opapp
                                           [EApp Opapp [EVar (Short "foldri_aux"); EVar (Short "v2")];
                                           EApp Opapp
                                             [EApp Opapp
                                                [EApp Opapp
                                                   [EVar (Short "v2");
                                                   ELet (Some "k")
                                                     (EApp (Opn Minus)
                                                        [EVar (Short "v3"); ELit (IntLit 1)])
                                                     (EIf
                                                        (EApp (Opb Lt)
                                                           [EVar (Short "k"); ELit (IntLit 0)])
                                                        (ELit (IntLit 0)) (EVar (Short "k")))];
                                                EApp Vsub
                                                  [EVar (Short "v4");
                                                  ELet (Some "k")
                                                    (EApp (Opn Minus)
                                                       [EVar (Short "v3"); ELit (IntLit 1)])
                                                    (EIf
                                                       (EApp (Opb Lt)
                                                          [EVar (Short "k"); ELit (IntLit 0)])
                                                       (ELit (IntLit 0)) (EVar (Short "k")))]];
                                             EVar (Short "v1")]]; EVar (Short "v4")];
                                     ELet (Some "k")
                                       (EApp (Opn Minus) [EVar (Short "v3"); ELit (IntLit 1)])
                                       (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                          (ELit (IntLit 0)) (EVar (Short "k")))])))))] "foldri_aux")
                    :: nsEmpty;
             sec := nsEmpty |} "v2"
             (EFun "v1"
                (EFun "v3"
                   (EApp Opapp
                      [EApp Opapp
                         [EApp Opapp
                            [EApp Opapp [EVar (Short "foldri_aux"); EVar (Short "v2")];
                            EVar (Short "v1")]; EVar (Short "v3")]; EApp Vlength [EVar (Short "v3")]]))));
           (Long "Vector" (Short "foldl"),
           Closure
             {|
             sev := (Short "foldl_aux",
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("foldl_aux", "v2",
                       EFun "v1"
                         (EFun "v5"
                            (EFun "v3"
                               (EFun "v4"
                                  (EIf (EApp Equality [EVar (Short "v4"); ELit (IntLit 0)])
                                     (EVar (Short "v1"))
                                     (EApp Opapp
                                        [EApp Opapp
                                           [EApp Opapp
                                              [EApp Opapp
                                                 [EApp Opapp
                                                    [EVar (Short "foldl_aux"); EVar (Short "v2")];
                                                 EApp Opapp
                                                   [EApp Opapp [EVar (Short "v2"); EVar (Short "v1")];
                                                   EApp Vsub [EVar (Short "v5"); EVar (Short "v3")]]];
                                              EVar (Short "v5")];
                                           EApp (Opn Plus) [EVar (Short "v3"); ELit (IntLit 1)]];
                                        ELet (Some "k")
                                          (EApp (Opn Minus) [EVar (Short "v4"); ELit (IntLit 1)])
                                          (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                             (ELit (IntLit 0)) (EVar (Short "k")))]))))))] "foldl_aux")
                    :: nsEmpty;
             sec := nsEmpty |} "v2"
             (EFun "v1"
                (EFun "v3"
                   (EApp Opapp
                      [EApp Opapp
                         [EApp Opapp
                            [EApp Opapp
                               [EApp Opapp [EVar (Short "foldl_aux"); EVar (Short "v2")];
                               EVar (Short "v1")]; EVar (Short "v3")]; ELit (IntLit 0)];
                      EApp Vlength [EVar (Short "v3")]]))));
           (Long "Vector" (Short "foldli"),
           Closure
             {|
             sev := (Short "foldli_aux_1",
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("foldli_aux_1", "v2",
                       EFun "v1"
                         (EFun "v5"
                            (EFun "v3"
                               (EFun "v4"
                                  (EIf (EApp Equality [EVar (Short "v4"); ELit (IntLit 0)])
                                     (EVar (Short "v1"))
                                     (EApp Opapp
                                        [EApp Opapp
                                           [EApp Opapp
                                              [EApp Opapp
                                                 [EApp Opapp
                                                    [EVar (Short "foldli_aux_1"); EVar (Short "v2")];
                                                 EApp Opapp
                                                   [EApp Opapp
                                                      [EApp Opapp
                                                         [EVar (Short "v2"); EVar (Short "v3")];
                                                      EApp Vsub [EVar (Short "v5"); EVar (Short "v3")]];
                                                   EVar (Short "v1")]]; EVar (Short "v5")];
                                           EApp (Opn Plus) [EVar (Short "v3"); ELit (IntLit 1)]];
                                        ELet (Some "k")
                                          (EApp (Opn Minus) [EVar (Short "v4"); ELit (IntLit 1)])
                                          (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                             (ELit (IntLit 0)) (EVar (Short "k")))]))))))]
                      "foldli_aux_1") :: nsEmpty;
             sec := nsEmpty |} "v2"
             (EFun "v1"
                (EFun "v3"
                   (EApp Opapp
                      [EApp Opapp
                         [EApp Opapp
                            [EApp Opapp
                               [EApp Opapp [EVar (Short "foldli_aux_1"); EVar (Short "v2")];
                               EVar (Short "v1")]; EVar (Short "v3")]; ELit (IntLit 0)];
                      EApp Vlength [EVar (Short "v3")]]))));
           (Long "Vector" (Short "mapi"),
           Closure
             {|
             sev := (Long "List" (Short "mapi"),
                    Closure
                      {|
                      sev := (Short "mapi",
                             Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                               [("mapi", "v4",
                                EFun "v5"
                                  (EFun "v6"
                                     (EMat (EVar (Short "v6"))
                                        [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                                        (Pcon (Some (Short "::")) [Pvar "v3"; Pvar "v2"],
                                        ELet (Some "v1")
                                          (EApp Opapp
                                             [EApp Opapp [EVar (Short "v4"); EVar (Short "v5")];
                                             EVar (Short "v3")])
                                          (ECon (Some (Short "::"))
                                             [EVar (Short "v1");
                                             EApp Opapp
                                               [EApp Opapp
                                                  [EApp Opapp [EVar (Short "mapi"); EVar (Short "v4")];
                                                  EApp (Opn Plus) [EVar (Short "v5"); ELit (IntLit 1)]];
                                               EVar (Short "v2")]]))])))] "mapi") :: nsEmpty;
                      sec := nsEmpty |} "v1"
                      (EFun "v2"
                         (EApp Opapp
                            [EApp Opapp
                               [EApp Opapp [EVar (Short "mapi"); EVar (Short "v1")]; ELit (IntLit 0)];
                            EVar (Short "v2")])))
                    :: (Short "toList",
                       Closure
                         {|
                         sev := (Short "tolist_aux",
                                Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                                  [("tolist_aux", "v2",
                                   EFun "v1"
                                     (EIf
                                        (EApp (Opb Leq)
                                           [EApp Vlength [EVar (Short "v2")]; EVar (Short "v1")])
                                        (ECon (Some (Short "[]")) [])
                                        (ECon (Some (Short "::"))
                                           [EApp Vsub [EVar (Short "v2"); EVar (Short "v1")];
                                           EApp Opapp
                                             [EApp Opapp [EVar (Short "tolist_aux"); EVar (Short "v2")];
                                             EApp (Opn Plus) [EVar (Short "v1"); ELit (IntLit 1)]]])))]
                                  "tolist_aux") :: nsEmpty;
                         sec := nsEmpty |} "v1"
                         (EApp Opapp
                            [EApp Opapp [EVar (Short "tolist_aux"); EVar (Short "v1")];
                            ELit (IntLit 0)])) :: nsEmpty;
             sec := nsEmpty |} "v2"
             (EFun "v1"
                (EApp VfromList
                   [EApp Opapp
                      [EApp Opapp [EVar (Long "List" (Short "mapi")); EVar (Short "v1")];
                      EApp Opapp [EVar (Short "toList"); EVar (Short "v2")]]])));
           (Long "Vector" (Short "map"),
           Closure
             {|
             sev := (Long "List" (Short "map"),
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("map", "v4",
                       EFun "v5"
                         (EMat (EVar (Short "v5"))
                            [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                            (Pcon (Some (Short "::")) [Pvar "v3"; Pvar "v2"],
                            ELet (Some "v1") (EApp Opapp [EVar (Short "v4"); EVar (Short "v3")])
                              (ECon (Some (Short "::"))
                                 [EVar (Short "v1");
                                 EApp Opapp
                                   [EApp Opapp [EVar (Short "map"); EVar (Short "v4")];
                                   EVar (Short "v2")]]))]))] "map")
                    :: (Short "toList",
                       Closure
                         {|
                         sev := (Short "tolist_aux",
                                Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                                  [("tolist_aux", "v2",
                                   EFun "v1"
                                     (EIf
                                        (EApp (Opb Leq)
                                           [EApp Vlength [EVar (Short "v2")]; EVar (Short "v1")])
                                        (ECon (Some (Short "[]")) [])
                                        (ECon (Some (Short "::"))
                                           [EApp Vsub [EVar (Short "v2"); EVar (Short "v1")];
                                           EApp Opapp
                                             [EApp Opapp [EVar (Short "tolist_aux"); EVar (Short "v2")];
                                             EApp (Opn Plus) [EVar (Short "v1"); ELit (IntLit 1)]]])))]
                                  "tolist_aux") :: nsEmpty;
                         sec := nsEmpty |} "v1"
                         (EApp Opapp
                            [EApp Opapp [EVar (Short "tolist_aux"); EVar (Short "v1")];
                            ELit (IntLit 0)])) :: nsEmpty;
             sec := nsEmpty |} "v2"
             (EFun "v1"
                (EApp VfromList
                   [EApp Opapp
                      [EApp Opapp [EVar (Long "List" (Short "map")); EVar (Short "v1")];
                      EApp Opapp [EVar (Short "toList"); EVar (Short "v2")]]])));
           (Long "Vector" (Short "concat"),
           Closure
             {|
             sev := (Long "List" (Short "concat"),
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("concat", "v3",
                       EMat (EVar (Short "v3"))
                         [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                         (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                         EApp ListAppend
                           [EVar (Short "v2"); EApp Opapp [EVar (Short "concat"); EVar (Short "v1")]])])]
                      "concat")
                    :: (Long "List" (Short "map"),
                       Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                         [("map", "v4",
                          EFun "v5"
                            (EMat (EVar (Short "v5"))
                               [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                               (Pcon (Some (Short "::")) [Pvar "v3"; Pvar "v2"],
                               ELet (Some "v1") (EApp Opapp [EVar (Short "v4"); EVar (Short "v3")])
                                 (ECon (Some (Short "::"))
                                    [EVar (Short "v1");
                                    EApp Opapp
                                      [EApp Opapp [EVar (Short "map"); EVar (Short "v4")];
                                      EVar (Short "v2")]]))]))] "map")
                       :: (Short "toList",
                          Closure
                            {|
                            sev := (Short "tolist_aux",
                                   Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                                     [("tolist_aux", "v2",
                                      EFun "v1"
                                        (EIf
                                           (EApp (Opb Leq)
                                              [EApp Vlength [EVar (Short "v2")]; EVar (Short "v1")])
                                           (ECon (Some (Short "[]")) [])
                                           (ECon (Some (Short "::"))
                                              [EApp Vsub [EVar (Short "v2"); EVar (Short "v1")];
                                              EApp Opapp
                                                [EApp Opapp
                                                   [EVar (Short "tolist_aux"); EVar (Short "v2")];
                                                EApp (Opn Plus) [EVar (Short "v1"); ELit (IntLit 1)]]])))]
                                     "tolist_aux") :: nsEmpty;
                            sec := nsEmpty |} "v1"
                            (EApp Opapp
                               [EApp Opapp [EVar (Short "tolist_aux"); EVar (Short "v1")];
                               ELit (IntLit 0)])) :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EApp VfromList
                [EApp Opapp
                   [EVar (Long "List" (Short "concat"));
                   EApp Opapp
                     [EApp Opapp [EVar (Long "List" (Short "map")); EVar (Short "toList")];
                     EVar (Short "v1")]]]));
           (Long "Vector" (Short "update"),
           Closure
             {|
             sev := (Long "List" (Short "update"),
                    Recclosure
                      {|
                      sev := (Short "update",
                             Closure {| sev := []; sec := [] |} "v3"
                               (EFun "v4"
                                  (EFun "v2"
                                     (EFun "v1"
                                        (EIf (EApp Equality [EVar (Short "v3"); EVar (Short "v1")])
                                           (EVar (Short "v4"))
                                           (EApp Opapp [EVar (Short "v2"); EVar (Short "v1")]))))))
                             :: nsEmpty;
                      sec := nsEmpty |}
                      [("update", "v8",
                       EFun "v9"
                         (EFun "v7"
                            (EMat (ECon None [EVar (Short "v9"); EVar (Short "v7")])
                               [(Pcon None [Pvar "v6"; Pvar "v5"],
                                EIf (EApp Equality [EVar (Short "v6"); ELit (IntLit 0)])
                                  (EMat (EVar (Short "v5"))
                                     [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                                     (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                                     ECon (Some (Short "::")) [EVar (Short "v8"); EVar (Short "v1")])])
                                  (EMat (EVar (Short "v5"))
                                     [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                                     (Pcon (Some (Short "::")) [Pvar "v4"; Pvar "v3"],
                                     ECon (Some (Short "::"))
                                       [EVar (Short "v4");
                                       EApp Opapp
                                         [EApp Opapp
                                            [EApp Opapp [EVar (Short "update"); EVar (Short "v8")];
                                            ELet (Some "k")
                                              (EApp (Opn Minus) [EVar (Short "v6"); ELit (IntLit 1)])
                                              (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                                 (ELit (IntLit 0)) (EVar (Short "k")))];
                                         EVar (Short "v3")]])]))])))] "update")
                    :: (Short "toList",
                       Closure
                         {|
                         sev := (Short "tolist_aux",
                                Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                                  [("tolist_aux", "v2",
                                   EFun "v1"
                                     (EIf
                                        (EApp (Opb Leq)
                                           [EApp Vlength [EVar (Short "v2")]; EVar (Short "v1")])
                                        (ECon (Some (Short "[]")) [])
                                        (ECon (Some (Short "::"))
                                           [EApp Vsub [EVar (Short "v2"); EVar (Short "v1")];
                                           EApp Opapp
                                             [EApp Opapp [EVar (Short "tolist_aux"); EVar (Short "v2")];
                                             EApp (Opn Plus) [EVar (Short "v1"); ELit (IntLit 1)]]])))]
                                  "tolist_aux") :: nsEmpty;
                         sec := nsEmpty |} "v1"
                         (EApp Opapp
                            [EApp Opapp [EVar (Short "tolist_aux"); EVar (Short "v1")];
                            ELit (IntLit 0)])) :: nsEmpty;
             sec := nsEmpty |} "v2"
             (EFun "v1"
                (EFun "v3"
                   (EApp VfromList
                      [EApp Opapp
                         [EApp Opapp
                            [EApp Opapp [EVar (Long "List" (Short "update")); EVar (Short "v3")];
                            EVar (Short "v1")]; EApp Opapp [EVar (Short "toList"); EVar (Short "v2")]]]))));
           (Long "Vector" (Short "toList"),
           Closure
             {|
             sev := (Short "tolist_aux",
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("tolist_aux", "v2",
                       EFun "v1"
                         (EIf (EApp (Opb Leq) [EApp Vlength [EVar (Short "v2")]; EVar (Short "v1")])
                            (ECon (Some (Short "[]")) [])
                            (ECon (Some (Short "::"))
                               [EApp Vsub [EVar (Short "v2"); EVar (Short "v1")];
                               EApp Opapp
                                 [EApp Opapp [EVar (Short "tolist_aux"); EVar (Short "v2")];
                                 EApp (Opn Plus) [EVar (Short "v1"); ELit (IntLit 1)]]])))]
                      "tolist_aux") :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EApp Opapp [EApp Opapp [EVar (Short "tolist_aux"); EVar (Short "v1")]; ELit (IntLit 0)]));
           (Long "Vector" (Short "tabulate"),
           Closure
             {|
             sev := (Long "List" (Short "genlist"),
                    Closure
                      {|
                      sev := (Short "genlist_aux",
                             Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                               [("genlist_aux", "v1",
                                EFun "v3"
                                  (EFun "v2"
                                     (EIf (EApp Equality [EVar (Short "v3"); ELit (IntLit 0)])
                                        (EVar (Short "v2"))
                                        (EApp Opapp
                                           [EApp Opapp
                                              [EApp Opapp
                                                 [EVar (Short "genlist_aux"); EVar (Short "v1")];
                                              ELet (Some "k")
                                                (EApp (Opn Minus) [EVar (Short "v3"); ELit (IntLit 1)])
                                                (EIf
                                                   (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                                   (ELit (IntLit 0)) (EVar (Short "k")))];
                                           ECon (Some (Short "::"))
                                             [EApp Opapp
                                                [EVar (Short "v1");
                                                ELet (Some "k")
                                                  (EApp (Opn Minus)
                                                     [EVar (Short "v3"); ELit (IntLit 1)])
                                                  (EIf
                                                     (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                                     (ELit (IntLit 0)) (EVar (Short "k")))];
                                             EVar (Short "v2")]]))))] "genlist_aux") :: nsEmpty;
                      sec := nsEmpty |} "v1"
                      (EFun "v2"
                         (EApp Opapp
                            [EApp Opapp
                               [EApp Opapp [EVar (Short "genlist_aux"); EVar (Short "v1")];
                               EVar (Short "v2")]; ECon (Some (Short "[]")) []]))) :: nsEmpty;
             sec := nsEmpty |} "v2"
             (EFun "v1"
                (EApp VfromList
                   [EApp Opapp
                      [EApp Opapp [EVar (Long "List" (Short "genlist")); EVar (Short "v1")];
                      EVar (Short "v2")]])));
           (Long "Vector" (Short "sub"),
           Closure {| sev := nsEmpty; sec := nsEmpty |} "v1"
             (EFun "v2" (EApp Vsub [EVar (Short "v1"); EVar (Short "v2")])));
           (Long "Vector" (Short "length"),
           Closure {| sev := nsEmpty; sec := nsEmpty |} "v1" (EApp Vlength [EVar (Short "v1")]));
           (Long "Vector" (Short "fromList"),
           Closure {| sev := nsEmpty; sec := nsEmpty |} "v1" (EApp VfromList [EVar (Short "v1")]));
           (Long "Alist" (Short "delete"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("delete", "v5",
              EFun "v6"
                (EMat (EVar (Short "v5"))
                   [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::")) [Pvar "v4"; Pvar "v3"],
                   EMat (EVar (Short "v4"))
                     [(Pcon None [Pvar "v2"; Pvar "v1"],
                      EIf (EApp Equality [EVar (Short "v2"); EVar (Short "v6")])
                        (EApp Opapp
                           [EApp Opapp [EVar (Short "delete"); EVar (Short "v3")]; EVar (Short "v6")])
                        (ECon (Some (Short "::"))
                           [ECon None [EVar (Short "v2"); EVar (Short "v1")];
                           EApp Opapp
                             [EApp Opapp [EVar (Short "delete"); EVar (Short "v3")]; EVar (Short "v6")]]))])]))]
             "delete");
           (Long "Alist" (Short "map"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("map", "v5",
              EFun "v6"
                (EMat (EVar (Short "v6"))
                   [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::")) [Pvar "v4"; Pvar "v3"],
                   EMat (EVar (Short "v4"))
                     [(Pcon None [Pvar "v2"; Pvar "v1"],
                      ECon (Some (Short "::"))
                        [ECon None
                           [EVar (Short "v2"); EApp Opapp [EVar (Short "v5"); EVar (Short "v1")]];
                        EApp Opapp
                          [EApp Opapp [EVar (Short "map"); EVar (Short "v5")]; EVar (Short "v3")]])])]))]
             "map");
           (Long "Alist" (Short "every"),
           Closure
             {|
             sev := (Short "every",
                    Recclosure
                      {|
                      sev := (Long "List" (Short "member"),
                             Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                               [("member", "v4",
                                EFun "v3"
                                  (EMat (EVar (Short "v3"))
                                     [(Pcon (Some (Short "[]")) [],
                                      EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]);
                                     (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                                     ELog Or (EApp Equality [EVar (Short "v4"); EVar (Short "v2")])
                                       (EApp Opapp
                                          [EApp Opapp [EVar (Short "member"); EVar (Short "v4")];
                                          EVar (Short "v1")]))]))] "member") :: nsEmpty;
                      sec := nsEmpty |}
                      [("every", "v5",
                       EFun "v6"
                         (EFun "v7"
                            (EMat (EVar (Short "v7"))
                               [(Pcon (Some (Short "[]")) [],
                                EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)]);
                               (Pcon (Some (Short "::")) [Pvar "v4"; Pvar "v3"],
                               EMat (EVar (Short "v4"))
                                 [(Pcon None [Pvar "v2"; Pvar "v1"],
                                  EIf
                                    (EApp Opapp
                                       [EApp Opapp
                                          [EVar (Long "List" (Short "member")); EVar (Short "v2")];
                                       EVar (Short "v5")])
                                    (EApp Opapp
                                       [EApp Opapp
                                          [EApp Opapp [EVar (Short "every"); EVar (Short "v5")];
                                          EVar (Short "v6")]; EVar (Short "v3")])
                                    (ELog And
                                       (EApp Opapp
                                          [EVar (Short "v6");
                                          ECon None [EVar (Short "v2"); EVar (Short "v1")]])
                                       (EApp Opapp
                                          [EApp Opapp
                                             [EApp Opapp
                                                [EVar (Short "every");
                                                ECon (Some (Short "::"))
                                                  [EVar (Short "v2"); EVar (Short "v5")]];
                                             EVar (Short "v6")]; EVar (Short "v3")])))])])))] "every")
                    :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EApp Opapp
                [EApp Opapp [EVar (Short "every"); ECon (Some (Short "[]")) []]; EVar (Short "v1")]));
           (Long "Alist" (Short "every"),
           Recclosure
             {|
             sev := (Long "List" (Short "member"),
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("member", "v4",
                       EFun "v3"
                         (EMat (EVar (Short "v3"))
                            [(Pcon (Some (Short "[]")) [],
                             EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]);
                            (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                            ELog Or (EApp Equality [EVar (Short "v4"); EVar (Short "v2")])
                              (EApp Opapp
                                 [EApp Opapp [EVar (Short "member"); EVar (Short "v4")];
                                 EVar (Short "v1")]))]))] "member") :: nsEmpty;
             sec := nsEmpty |}
             [("every", "v5",
              EFun "v6"
                (EFun "v7"
                   (EMat (EVar (Short "v7"))
                      [(Pcon (Some (Short "[]")) [], EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)]);
                      (Pcon (Some (Short "::")) [Pvar "v4"; Pvar "v3"],
                      EMat (EVar (Short "v4"))
                        [(Pcon None [Pvar "v2"; Pvar "v1"],
                         EIf
                           (EApp Opapp
                              [EApp Opapp [EVar (Long "List" (Short "member")); EVar (Short "v2")];
                              EVar (Short "v5")])
                           (EApp Opapp
                              [EApp Opapp
                                 [EApp Opapp [EVar (Short "every"); EVar (Short "v5")];
                                 EVar (Short "v6")]; EVar (Short "v3")])
                           (ELog And
                              (EApp Opapp
                                 [EVar (Short "v6"); ECon None [EVar (Short "v2"); EVar (Short "v1")]])
                              (EApp Opapp
                                 [EApp Opapp
                                    [EApp Opapp
                                       [EVar (Short "every");
                                       ECon (Some (Short "::")) [EVar (Short "v2"); EVar (Short "v5")]];
                                    EVar (Short "v6")]; EVar (Short "v3")])))])])))] "every");
           (Long "Alist" (Short "update"),
           Closure {| sev := nsEmpty; sec := nsEmpty |} "v3"
             (EFun "v4"
                (EMat (EVar (Short "v4"))
                   [(Pcon None [Pvar "v2"; Pvar "v1"],
                    ECon (Some (Short "::"))
                      [ECon None [EVar (Short "v2"); EVar (Short "v1")]; EVar (Short "v3")])])));
           (Long "Alist" (Short "lookup"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("lookup", "v5",
              EFun "v6"
                (EMat (EVar (Short "v5"))
                   [(Pcon (Some (Short "[]")) [], ECon (Some (Short "None")) []);
                   (Pcon (Some (Short "::")) [Pvar "v4"; Pvar "v3"],
                   EMat (EVar (Short "v4"))
                     [(Pcon None [Pvar "v2"; Pvar "v1"],
                      EIf (EApp Equality [EVar (Short "v2"); EVar (Short "v6")])
                        (ECon (Some (Short "Some")) [EVar (Short "v1")])
                        (EApp Opapp
                           [EApp Opapp [EVar (Short "lookup"); EVar (Short "v3")]; EVar (Short "v6")]))])]))]
             "lookup");
           (Long "List" (Short "sort"),
           Recclosure
             {|
             sev := (Short "partition_1",
                    Closure
                      {|
                      sev := (Short "part",
                             Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                               [("part", "v3",
                                EFun "v6"
                                  (EFun "v4"
                                     (EFun "v5"
                                        (EMat (EVar (Short "v6"))
                                           [(Pcon (Some (Short "[]")) [],
                                            ECon None [EVar (Short "v4"); EVar (Short "v5")]);
                                           (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                                           EIf (EApp Opapp [EVar (Short "v3"); EVar (Short "v2")])
                                             (EApp Opapp
                                                [EApp Opapp
                                                   [EApp Opapp
                                                      [EApp Opapp
                                                         [EVar (Short "part"); EVar (Short "v3")];
                                                      EVar (Short "v1")];
                                                   ECon (Some (Short "::"))
                                                     [EVar (Short "v2"); EVar (Short "v4")]];
                                                EVar (Short "v5")])
                                             (EApp Opapp
                                                [EApp Opapp
                                                   [EApp Opapp
                                                      [EApp Opapp
                                                         [EVar (Short "part"); EVar (Short "v3")];
                                                      EVar (Short "v1")]; EVar (Short "v4")];
                                                ECon (Some (Short "::"))
                                                  [EVar (Short "v2"); EVar (Short "v5")]]))]))))]
                               "part") :: nsEmpty;
                      sec := nsEmpty |} "v1"
                      (EFun "v2"
                         (EApp Opapp
                            [EApp Opapp
                               [EApp Opapp
                                  [EApp Opapp [EVar (Short "part"); EVar (Short "v1")];
                                  EVar (Short "v2")]; ECon (Some (Short "[]")) []];
                            ECon (Some (Short "[]")) []]))) :: nsEmpty;
             sec := nsEmpty |}
             [("sort", "v7",
              EFun "v8"
                (EMat (EVar (Short "v8"))
                   [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::")) [Pvar "v6"; Pvar "v5"],
                   ELet (Some "v3")
                     (EApp Opapp
                        [EApp Opapp
                           [EVar (Short "partition_1");
                           EFun "v4"
                             (EApp Opapp
                                [EApp Opapp [EVar (Short "v7"); EVar (Short "v4")]; EVar (Short "v6")])];
                        EVar (Short "v5")])
                     (EMat (EVar (Short "v3"))
                        [(Pcon None [Pvar "v2"; Pvar "v1"],
                         EApp ListAppend
                           [EApp ListAppend
                              [EApp Opapp
                                 [EApp Opapp [EVar (Short "sort"); EVar (Short "v7")];
                                 EVar (Short "v2")];
                              ECon (Some (Short "::")) [EVar (Short "v6"); ECon (Some (Short "[]")) []]];
                           EApp Opapp
                             [EApp Opapp [EVar (Short "sort"); EVar (Short "v7")]; EVar (Short "v1")]])]))]))]
             "sort");
           (Long "List" (Short "compare"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("compare", "v7",
              EFun "v8"
                (EFun "v9"
                   (EMat (EVar (Short "v8"))
                      [(Pcon (Some (Short "[]")) [],
                       EMat (EVar (Short "v9"))
                         [(Pcon (Some (Short "[]")) [], ECon (Some (Short "Equal")) []);
                         (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                         ECon (Some (Short "Less")) [])]);
                      (Pcon (Some (Short "::")) [Pvar "v6"; Pvar "v5"],
                      EMat (EVar (Short "v9"))
                        [(Pcon (Some (Short "[]")) [], ECon (Some (Short "Greater")) []);
                        (Pcon (Some (Short "::")) [Pvar "v4"; Pvar "v3"],
                        EMat
                          (EApp Opapp
                             [EApp Opapp [EVar (Short "v7"); EVar (Short "v6")]; EVar (Short "v4")])
                          [(Pcon (Some (Short "Less")) [], ECon (Some (Short "Less")) []);
                          (Pcon (Some (Short "Equal")) [],
                          EApp Opapp
                            [EApp Opapp
                               [EApp Opapp [EVar (Short "compare"); EVar (Short "v7")];
                               EVar (Short "v5")]; EVar (Short "v3")]);
                          (Pcon (Some (Short "Greater")) [], ECon (Some (Short "Greater")) [])])])])))]
             "compare");
           (Long "List" (Short "update"),
           Recclosure
             {|
             sev := (Short "update",
                    Closure {| sev := []; sec := [] |} "v3"
                      (EFun "v4"
                         (EFun "v2"
                            (EFun "v1"
                               (EIf (EApp Equality [EVar (Short "v3"); EVar (Short "v1")])
                                  (EVar (Short "v4"))
                                  (EApp Opapp [EVar (Short "v2"); EVar (Short "v1")])))))) :: nsEmpty;
             sec := nsEmpty |}
             [("update", "v8",
              EFun "v9"
                (EFun "v7"
                   (EMat (ECon None [EVar (Short "v9"); EVar (Short "v7")])
                      [(Pcon None [Pvar "v6"; Pvar "v5"],
                       EIf (EApp Equality [EVar (Short "v6"); ELit (IntLit 0)])
                         (EMat (EVar (Short "v5"))
                            [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                            (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                            ECon (Some (Short "::")) [EVar (Short "v8"); EVar (Short "v1")])])
                         (EMat (EVar (Short "v5"))
                            [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                            (Pcon (Some (Short "::")) [Pvar "v4"; Pvar "v3"],
                            ECon (Some (Short "::"))
                              [EVar (Short "v4");
                              EApp Opapp
                                [EApp Opapp
                                   [EApp Opapp [EVar (Short "update"); EVar (Short "v8")];
                                   ELet (Some "k")
                                     (EApp (Opn Minus) [EVar (Short "v6"); ELit (IntLit 1)])
                                     (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                        (ELit (IntLit 0)) (EVar (Short "k")))];
                                EVar (Short "v3")]])]))])))] "update");
           (Long "List" (Short "splitAtPki"),
           Recclosure
             {|
             sev := (Short "o",
                    Closure {| sev := []; sec := [] |} "v2"
                      (EFun "v3"
                         (EFun "v1"
                            (EApp Opapp
                               [EVar (Short "v2"); EApp Opapp [EVar (Short "v3"); EVar (Short "v1")]]))))
                    :: nsEmpty;
             sec := nsEmpty |}
             [("splitAtPki", "v6",
              EFun "v7"
                (EFun "v8"
                   (EMat (EVar (Short "v8"))
                      [(Pcon (Some (Short "[]")) [],
                       EApp Opapp
                         [EApp Opapp [EVar (Short "v7"); ECon (Some (Short "[]")) []];
                         ECon (Some (Short "[]")) []]);
                      (Pcon (Some (Short "::")) [Pvar "v5"; Pvar "v4"],
                      EIf
                        (EApp Opapp
                           [EApp Opapp [EVar (Short "v6"); ELit (IntLit 0)]; EVar (Short "v5")])
                        (EApp Opapp
                           [EApp Opapp [EVar (Short "v7"); ECon (Some (Short "[]")) []];
                           ECon (Some (Short "::")) [EVar (Short "v5"); EVar (Short "v4")]])
                        (EApp Opapp
                           [EApp Opapp
                              [EApp Opapp
                                 [EVar (Short "splitAtPki");
                                 EApp Opapp
                                   [EApp Opapp [EVar (Short "o"); EVar (Short "v6")];
                                   EFun "v1" (EApp (Opn Plus) [EVar (Short "v1"); ELit (IntLit 1)])]];
                              EFun "v3"
                                (EFun "v2"
                                   (EApp Opapp
                                      [EApp Opapp
                                         [EVar (Short "v7");
                                         ECon (Some (Short "::"))
                                           [EVar (Short "v5"); EVar (Short "v3")]];
                                      EVar (Short "v2")]))]; EVar (Short "v4")]))])))] "splitAtPki");
           (Long "List" (Short "front"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("front", "x0",
              EMat (EVar (Short "x0"))
                [(Pcon (Some (Short "[]")) [], ERaise (ECon (Some (Short "Bind")) []));
                (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                EIf (EApp Equality [EVar (Short "v1"); ECon (Some (Short "[]")) []])
                  (ECon (Some (Short "[]")) [])
                  (ECon (Some (Short "::"))
                     [EVar (Short "v2"); EApp Opapp [EVar (Short "front"); EVar (Short "v1")]]))])]
             "front");
           (Long "List" (Short "isPrefix"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("isPrefix", "v5",
              EFun "v6"
                (EMat (EVar (Short "v5"))
                   [(Pcon (Some (Short "[]")) [], EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)]);
                   (Pcon (Some (Short "::")) [Pvar "v4"; Pvar "v3"],
                   EMat (EVar (Short "v6"))
                     [(Pcon (Some (Short "[]")) [], EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]);
                     (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                     ELog And (EApp Equality [EVar (Short "v4"); EVar (Short "v2")])
                       (EApp Opapp
                          [EApp Opapp [EVar (Short "isPrefix"); EVar (Short "v3")]; EVar (Short "v1")]))])]))]
             "isPrefix");
           (Long "List" (Short "all_distinct"),
           Recclosure
             {|
             sev := (Short "member",
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("member", "v4",
                       EFun "v3"
                         (EMat (EVar (Short "v3"))
                            [(Pcon (Some (Short "[]")) [],
                             EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]);
                            (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                            ELog Or (EApp Equality [EVar (Short "v4"); EVar (Short "v2")])
                              (EApp Opapp
                                 [EApp Opapp [EVar (Short "member"); EVar (Short "v4")];
                                 EVar (Short "v1")]))]))] "member") :: nsEmpty;
             sec := nsEmpty |}
             [("all_distinct", "v3",
              EMat (EVar (Short "v3"))
                [(Pcon (Some (Short "[]")) [], EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)]);
                (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                ELog And
                  (EApp Equality
                     [EApp Opapp
                        [EApp Opapp [EVar (Short "member"); EVar (Short "v2")]; EVar (Short "v1")];
                     EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]])
                  (EApp Opapp [EVar (Short "all_distinct"); EVar (Short "v1")]))])] "all_distinct");
           (Long "List" (Short "pad_left"),
           Closure
             {|
             sev := (Short "genlist",
                    Closure
                      {|
                      sev := (Short "genlist_aux",
                             Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                               [("genlist_aux", "v1",
                                EFun "v3"
                                  (EFun "v2"
                                     (EIf (EApp Equality [EVar (Short "v3"); ELit (IntLit 0)])
                                        (EVar (Short "v2"))
                                        (EApp Opapp
                                           [EApp Opapp
                                              [EApp Opapp
                                                 [EVar (Short "genlist_aux"); EVar (Short "v1")];
                                              ELet (Some "k")
                                                (EApp (Opn Minus) [EVar (Short "v3"); ELit (IntLit 1)])
                                                (EIf
                                                   (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                                   (ELit (IntLit 0)) (EVar (Short "k")))];
                                           ECon (Some (Short "::"))
                                             [EApp Opapp
                                                [EVar (Short "v1");
                                                ELet (Some "k")
                                                  (EApp (Opn Minus)
                                                     [EVar (Short "v3"); ELit (IntLit 1)])
                                                  (EIf
                                                     (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                                     (ELit (IntLit 0)) (EVar (Short "k")))];
                                             EVar (Short "v2")]]))))] "genlist_aux") :: nsEmpty;
                      sec := nsEmpty |} "v1"
                      (EFun "v2"
                         (EApp Opapp
                            [EApp Opapp
                               [EApp Opapp [EVar (Short "genlist_aux"); EVar (Short "v1")];
                               EVar (Short "v2")]; ECon (Some (Short "[]")) []])))
                    :: (Short "const",
                       Closure {| sev := []; sec := [] |} "v2" (EFun "v1" (EVar (Short "v2"))))
                       :: (Short "length",
                          Closure
                            {|
                            sev := (Short "length_aux",
                                   Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                                     [("length_aux", "v3",
                                      EFun "v4"
                                        (EMat (EVar (Short "v3"))
                                           [(Pcon (Some (Short "[]")) [], EVar (Short "v4"));
                                           (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                                           EApp Opapp
                                             [EApp Opapp [EVar (Short "length_aux"); EVar (Short "v1")];
                                             EApp (Opn Plus) [EVar (Short "v4"); ELit (IntLit 1)]])]))]
                                     "length_aux") :: nsEmpty;
                            sec := nsEmpty |} "v1"
                            (EApp Opapp
                               [EApp Opapp [EVar (Short "length_aux"); EVar (Short "v1")];
                               ELit (IntLit 0)])) :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EFun "v2"
                (EFun "v3"
                   (EApp ListAppend
                      [EApp Opapp
                         [EApp Opapp
                            [EVar (Short "genlist");
                            EApp Opapp [EVar (Short "const"); EVar (Short "v1")]];
                         ELet (Some "k")
                           (EApp (Opn Minus)
                              [EVar (Short "v2");
                              EApp Opapp [EVar (Short "length"); EVar (Short "v3")]])
                           (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                              (ELit (IntLit 0)) (EVar (Short "k")))]; EVar (Short "v3")]))));
           (Long "List" (Short "pad_right"),
           Closure
             {|
             sev := (Short "genlist",
                    Closure
                      {|
                      sev := (Short "genlist_aux",
                             Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                               [("genlist_aux", "v1",
                                EFun "v3"
                                  (EFun "v2"
                                     (EIf (EApp Equality [EVar (Short "v3"); ELit (IntLit 0)])
                                        (EVar (Short "v2"))
                                        (EApp Opapp
                                           [EApp Opapp
                                              [EApp Opapp
                                                 [EVar (Short "genlist_aux"); EVar (Short "v1")];
                                              ELet (Some "k")
                                                (EApp (Opn Minus) [EVar (Short "v3"); ELit (IntLit 1)])
                                                (EIf
                                                   (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                                   (ELit (IntLit 0)) (EVar (Short "k")))];
                                           ECon (Some (Short "::"))
                                             [EApp Opapp
                                                [EVar (Short "v1");
                                                ELet (Some "k")
                                                  (EApp (Opn Minus)
                                                     [EVar (Short "v3"); ELit (IntLit 1)])
                                                  (EIf
                                                     (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                                     (ELit (IntLit 0)) (EVar (Short "k")))];
                                             EVar (Short "v2")]]))))] "genlist_aux") :: nsEmpty;
                      sec := nsEmpty |} "v1"
                      (EFun "v2"
                         (EApp Opapp
                            [EApp Opapp
                               [EApp Opapp [EVar (Short "genlist_aux"); EVar (Short "v1")];
                               EVar (Short "v2")]; ECon (Some (Short "[]")) []])))
                    :: (Short "const",
                       Closure {| sev := []; sec := [] |} "v2" (EFun "v1" (EVar (Short "v2"))))
                       :: (Short "length",
                          Closure
                            {|
                            sev := (Short "length_aux",
                                   Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                                     [("length_aux", "v3",
                                      EFun "v4"
                                        (EMat (EVar (Short "v3"))
                                           [(Pcon (Some (Short "[]")) [], EVar (Short "v4"));
                                           (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                                           EApp Opapp
                                             [EApp Opapp [EVar (Short "length_aux"); EVar (Short "v1")];
                                             EApp (Opn Plus) [EVar (Short "v4"); ELit (IntLit 1)]])]))]
                                     "length_aux") :: nsEmpty;
                            sec := nsEmpty |} "v1"
                            (EApp Opapp
                               [EApp Opapp [EVar (Short "length_aux"); EVar (Short "v1")];
                               ELit (IntLit 0)])) :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EFun "v2"
                (EFun "v3"
                   (EApp ListAppend
                      [EVar (Short "v3");
                      EApp Opapp
                        [EApp Opapp
                           [EVar (Short "genlist");
                           EApp Opapp [EVar (Short "const"); EVar (Short "v1")]];
                        ELet (Some "k")
                          (EApp (Opn Minus)
                             [EVar (Short "v2"); EApp Opapp [EVar (Short "length"); EVar (Short "v3")]])
                          (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                             (ELit (IntLit 0)) (EVar (Short "k")))]]))));
           (Long "List" (Short "unzip"),
           Recclosure
             {|
             sev := (Short "fst",
                    Closure {| sev := []; sec := [] |} "v3"
                      (EMat (EVar (Short "v3")) [(Pcon None [Pvar "v2"; Pvar "v1"], EVar (Short "v2"))]))
                    :: (Short "fst",
                       Closure {| sev := []; sec := [] |} "v3"
                         (EMat (EVar (Short "v3"))
                            [(Pcon None [Pvar "v2"; Pvar "v1"], EVar (Short "v2"))]))
                       :: (Short "snd",
                          Closure {| sev := []; sec := [] |} "v3"
                            (EMat (EVar (Short "v3"))
                               [(Pcon None [Pvar "v2"; Pvar "v1"], EVar (Short "v1"))]))
                          :: (Short "snd",
                             Closure {| sev := []; sec := [] |} "v3"
                               (EMat (EVar (Short "v3"))
                                  [(Pcon None [Pvar "v2"; Pvar "v1"], EVar (Short "v1"))])) :: nsEmpty;
             sec := nsEmpty |}
             [("unzip", "v3",
              EMat (EVar (Short "v3"))
                [(Pcon (Some (Short "[]")) [],
                 ECon None [ECon (Some (Short "[]")) []; ECon (Some (Short "[]")) []]);
                (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                ECon None
                  [ECon (Some (Short "::"))
                     [EApp Opapp [EVar (Short "fst"); EVar (Short "v2")];
                     EApp Opapp
                       [EVar (Short "fst"); EApp Opapp [EVar (Short "unzip"); EVar (Short "v1")]]];
                  ECon (Some (Short "::"))
                    [EApp Opapp [EVar (Short "snd"); EVar (Short "v2")];
                    EApp Opapp
                      [EVar (Short "snd"); EApp Opapp [EVar (Short "unzip"); EVar (Short "v1")]]]])])]
             "unzip");
           (Long "List" (Short "sum"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("sum", "v3",
              EMat (EVar (Short "v3"))
                [(Pcon (Some (Short "[]")) [], ELit (IntLit 0));
                (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                EApp (Opn Plus) [EVar (Short "v2"); EApp Opapp [EVar (Short "sum"); EVar (Short "v1")]])])]
             "sum");
           (Long "List" (Short "member"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("member", "v4",
              EFun "v3"
                (EMat (EVar (Short "v3"))
                   [(Pcon (Some (Short "[]")) [], EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]);
                   (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                   ELog Or (EApp Equality [EVar (Short "v4"); EVar (Short "v2")])
                     (EApp Opapp
                        [EApp Opapp [EVar (Short "member"); EVar (Short "v4")]; EVar (Short "v1")]))]))]
             "member");
           (Long "List" (Short "zip"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("zip", "v9",
              EMat (EVar (Short "v9"))
                [(Pcon None [Pvar "v8"; Pvar "v7"],
                 EMat (EVar (Short "v8"))
                   [(Pcon (Some (Short "[]")) [],
                    EMat (EVar (Short "v7"))
                      [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                      (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"], ECon (Some (Short "[]")) [])]);
                   (Pcon (Some (Short "::")) [Pvar "v6"; Pvar "v5"],
                   EMat (EVar (Short "v7"))
                     [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                     (Pcon (Some (Short "::")) [Pvar "v4"; Pvar "v3"],
                     ECon (Some (Short "::"))
                       [ECon None [EVar (Short "v6"); EVar (Short "v4")];
                       EApp Opapp
                         [EVar (Short "zip"); ECon None [EVar (Short "v5"); EVar (Short "v3")]]])])])])]
             "zip");
           (Long "List" (Short "collate"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("collate", "v7",
              EFun "v8"
                (EFun "v9"
                   (EMat (EVar (Short "v8"))
                      [(Pcon (Some (Short "[]")) [],
                       EMat (EVar (Short "v9"))
                         [(Pcon (Some (Short "[]")) [], ECon (Some (Short "Equal")) []);
                         (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                         ECon (Some (Short "Less")) [])]);
                      (Pcon (Some (Short "::")) [Pvar "v6"; Pvar "v5"],
                      EMat (EVar (Short "v9"))
                        [(Pcon (Some (Short "[]")) [], ECon (Some (Short "Greater")) []);
                        (Pcon (Some (Short "::")) [Pvar "v4"; Pvar "v3"],
                        EIf
                          (EApp Equality
                             [EApp Opapp
                                [EApp Opapp [EVar (Short "v7"); EVar (Short "v6")]; EVar (Short "v4")];
                             ECon (Some (Short "Equal")) []])
                          (EApp Opapp
                             [EApp Opapp
                                [EApp Opapp [EVar (Short "collate"); EVar (Short "v7")];
                                EVar (Short "v5")]; EVar (Short "v3")])
                          (EApp Opapp
                             [EApp Opapp [EVar (Short "v7"); EVar (Short "v6")]; EVar (Short "v4")]))])])))]
             "collate");
           (Long "List" (Short "tabulate"),
           Closure
             {|
             sev := (Short "tabulate",
                    Recclosure
                      {|
                      sev := (Short "rev",
                             Closure
                               {|
                               sev := (Short "rev",
                                      Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                                        [("rev", "v4",
                                         EFun "v3"
                                           (EMat (EVar (Short "v4"))
                                              [(Pcon (Some (Short "[]")) [], EVar (Short "v3"));
                                              (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                                              EApp Opapp
                                                [EApp Opapp [EVar (Short "rev"); EVar (Short "v1")];
                                                ECon (Some (Short "::"))
                                                  [EVar (Short "v2"); EVar (Short "v3")]])]))] "rev")
                                      :: nsEmpty;
                               sec := nsEmpty |} "v1"
                               (EApp Opapp
                                  [EApp Opapp [EVar (Short "rev"); EVar (Short "v1")];
                                  ECon (Some (Short "[]")) []])) :: nsEmpty;
                      sec := nsEmpty |}
                      [("tabulate", "v8",
                       EFun "v7"
                         (EFun "v6"
                            (EFun "v5"
                               (ELet (Some "v4")
                                  (EApp (Opb Geq) [EVar (Short "v8"); EVar (Short "v7")])
                                  (EIf (EVar (Short "v4"))
                                     (EApp Opapp [EVar (Short "rev"); EVar (Short "v5")])
                                     (ELet (Some "v3")
                                        (EApp Opapp [EVar (Short "v6"); EVar (Short "v8")])
                                        (ELet (Some "v2")
                                           (EApp (Opn Plus) [EVar (Short "v8"); ELit (IntLit 1)])
                                           (ELet (Some "v1")
                                              (ECon (Some (Short "::"))
                                                 [EVar (Short "v3"); EVar (Short "v5")])
                                              (EApp Opapp
                                                 [EApp Opapp
                                                    [EApp Opapp
                                                       [EApp Opapp
                                                          [EVar (Short "tabulate"); EVar (Short "v2")];
                                                       EVar (Short "v7")];
                                                    EVar (Short "v6")]; EVar (Short "v1")])))))))))]
                      "tabulate") :: nsEmpty;
             sec := nsEmpty |} "v3"
             (EFun "v2"
                (ELet (Some "v1") (ECon (Some (Short "[]")) [])
                   (EApp Opapp
                      [EApp Opapp
                         [EApp Opapp
                            [EApp Opapp [EVar (Short "tabulate"); ELit (IntLit 0)]; EVar (Short "v3")];
                         EVar (Short "v2")]; EVar (Short "v1")]))));
           (Long "List" (Short "tabulate"),
           Recclosure
             {|
             sev := (Short "rev",
                    Closure
                      {|
                      sev := (Short "rev",
                             Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                               [("rev", "v4",
                                EFun "v3"
                                  (EMat (EVar (Short "v4"))
                                     [(Pcon (Some (Short "[]")) [], EVar (Short "v3"));
                                     (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                                     EApp Opapp
                                       [EApp Opapp [EVar (Short "rev"); EVar (Short "v1")];
                                       ECon (Some (Short "::")) [EVar (Short "v2"); EVar (Short "v3")]])]))]
                               "rev") :: nsEmpty;
                      sec := nsEmpty |} "v1"
                      (EApp Opapp
                         [EApp Opapp [EVar (Short "rev"); EVar (Short "v1")];
                         ECon (Some (Short "[]")) []])) :: nsEmpty;
             sec := nsEmpty |}
             [("tabulate", "v8",
              EFun "v7"
                (EFun "v6"
                   (EFun "v5"
                      (ELet (Some "v4") (EApp (Opb Geq) [EVar (Short "v8"); EVar (Short "v7")])
                         (EIf (EVar (Short "v4")) (EApp Opapp [EVar (Short "rev"); EVar (Short "v5")])
                            (ELet (Some "v3") (EApp Opapp [EVar (Short "v6"); EVar (Short "v8")])
                               (ELet (Some "v2") (EApp (Opn Plus) [EVar (Short "v8"); ELit (IntLit 1)])
                                  (ELet (Some "v1")
                                     (ECon (Some (Short "::")) [EVar (Short "v3"); EVar (Short "v5")])
                                     (EApp Opapp
                                        [EApp Opapp
                                           [EApp Opapp
                                              [EApp Opapp [EVar (Short "tabulate"); EVar (Short "v2")];
                                              EVar (Short "v7")]; EVar (Short "v6")];
                                        EVar (Short "v1")])))))))))] "tabulate");
           (Long "List" (Short "genlist"),
           Closure
             {|
             sev := (Short "genlist_aux",
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("genlist_aux", "v1",
                       EFun "v3"
                         (EFun "v2"
                            (EIf (EApp Equality [EVar (Short "v3"); ELit (IntLit 0)])
                               (EVar (Short "v2"))
                               (EApp Opapp
                                  [EApp Opapp
                                     [EApp Opapp [EVar (Short "genlist_aux"); EVar (Short "v1")];
                                     ELet (Some "k")
                                       (EApp (Opn Minus) [EVar (Short "v3"); ELit (IntLit 1)])
                                       (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                          (ELit (IntLit 0)) (EVar (Short "k")))];
                                  ECon (Some (Short "::"))
                                    [EApp Opapp
                                       [EVar (Short "v1");
                                       ELet (Some "k")
                                         (EApp (Opn Minus) [EVar (Short "v3"); ELit (IntLit 1)])
                                         (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                            (ELit (IntLit 0)) (EVar (Short "k")))];
                                    EVar (Short "v2")]]))))] "genlist_aux") :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EFun "v2"
                (EApp Opapp
                   [EApp Opapp
                      [EApp Opapp [EVar (Short "genlist_aux"); EVar (Short "v1")]; EVar (Short "v2")];
                   ECon (Some (Short "[]")) []])));
           (Long "List" (Short "snoc"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("snoc", "v4",
              EFun "v3"
                (EMat (EVar (Short "v3"))
                   [(Pcon (Some (Short "[]")) [],
                    ECon (Some (Short "::")) [EVar (Short "v4"); ECon (Some (Short "[]")) []]);
                   (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                   ECon (Some (Short "::"))
                     [EVar (Short "v2");
                     EApp Opapp
                       [EApp Opapp [EVar (Short "snoc"); EVar (Short "v4")]; EVar (Short "v1")]])]))]
             "snoc");
           (Long "List" (Short "all"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("all", "v3",
              EFun "v4"
                (EMat (EVar (Short "v4"))
                   [(Pcon (Some (Short "[]")) [], EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)]);
                   (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                   ELog And (EApp Opapp [EVar (Short "v3"); EVar (Short "v2")])
                     (EApp Opapp
                        [EApp Opapp [EVar (Short "all"); EVar (Short "v3")]; EVar (Short "v1")]))]))]
             "all");
           (Long "List" (Short "exists"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("exists", "v3",
              EFun "v4"
                (EMat (EVar (Short "v4"))
                   [(Pcon (Some (Short "[]")) [], EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]);
                   (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                   ELog Or (EApp Opapp [EVar (Short "v3"); EVar (Short "v2")])
                     (EApp Opapp
                        [EApp Opapp [EVar (Short "exists"); EVar (Short "v3")]; EVar (Short "v1")]))]))]
             "exists");
           (Long "List" (Short "foldri"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("foldri", "v5",
              EFun "v4"
                (EFun "v6"
                   (EMat (EVar (Short "v6"))
                      [(Pcon (Some (Short "[]")) [], EVar (Short "v4"));
                      (Pcon (Some (Short "::")) [Pvar "v3"; Pvar "v2"],
                      EApp Opapp
                        [EApp Opapp
                           [EApp Opapp [EVar (Short "v5"); ELit (IntLit 0)]; EVar (Short "v3")];
                        EApp Opapp
                          [EApp Opapp
                             [EApp Opapp
                                [EVar (Short "foldri");
                                EFun "v1"
                                  (EApp Opapp
                                     [EVar (Short "v5");
                                     EApp (Opn Plus) [EVar (Short "v1"); ELit (IntLit 1)]])];
                             EVar (Short "v4")]; EVar (Short "v2")]])])))] "foldri");
           (Long "List" (Short "foldr"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("foldr", "v4",
              EFun "v3"
                (EFun "v5"
                   (EMat (EVar (Short "v5"))
                      [(Pcon (Some (Short "[]")) [], EVar (Short "v3"));
                      (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                      EApp Opapp
                        [EApp Opapp [EVar (Short "v4"); EVar (Short "v2")];
                        EApp Opapp
                          [EApp Opapp
                             [EApp Opapp [EVar (Short "foldr"); EVar (Short "v4")]; EVar (Short "v3")];
                          EVar (Short "v1")]])])))] "foldr");
           (Long "List" (Short "foldi"),
           Closure
             {|
             sev := (Short "foldli_aux",
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("foldli_aux", "v4",
                       EFun "v3"
                         (EFun "v5"
                            (EFun "v6"
                               (EMat (EVar (Short "v6"))
                                  [(Pcon (Some (Short "[]")) [], EVar (Short "v3"));
                                  (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                                  EApp Opapp
                                    [EApp Opapp
                                       [EApp Opapp
                                          [EApp Opapp [EVar (Short "foldli_aux"); EVar (Short "v4")];
                                          EApp Opapp
                                            [EApp Opapp
                                               [EApp Opapp [EVar (Short "v4"); EVar (Short "v5")];
                                               EVar (Short "v2")]; EVar (Short "v3")]];
                                       EApp (Opn Plus) [EVar (Short "v5"); ELit (IntLit 1)]];
                                    EVar (Short "v1")])]))))] "foldli_aux") :: nsEmpty;
             sec := nsEmpty |} "v2"
             (EFun "v1"
                (EFun "v3"
                   (EApp Opapp
                      [EApp Opapp
                         [EApp Opapp
                            [EApp Opapp [EVar (Short "foldli_aux"); EVar (Short "v2")];
                            EVar (Short "v1")]; ELit (IntLit 0)]; EVar (Short "v3")]))));
           (Long "List" (Short "foldl"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("foldl", "v4",
              EFun "v3"
                (EFun "v5"
                   (EMat (EVar (Short "v5"))
                      [(Pcon (Some (Short "[]")) [], EVar (Short "v3"));
                      (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                      EApp Opapp
                        [EApp Opapp
                           [EApp Opapp [EVar (Short "foldl"); EVar (Short "v4")];
                           EApp Opapp
                             [EApp Opapp [EVar (Short "v4"); EVar (Short "v3")]; EVar (Short "v2")]];
                        EVar (Short "v1")])])))] "foldl");
           (Long "List" (Short "partition"),
           Closure
             {|
             sev := (Short "partition_aux",
                    Recclosure
                      {|
                      sev := (Short "rev",
                             Closure
                               {|
                               sev := (Short "rev",
                                      Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                                        [("rev", "v4",
                                         EFun "v3"
                                           (EMat (EVar (Short "v4"))
                                              [(Pcon (Some (Short "[]")) [], EVar (Short "v3"));
                                              (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                                              EApp Opapp
                                                [EApp Opapp [EVar (Short "rev"); EVar (Short "v1")];
                                                ECon (Some (Short "::"))
                                                  [EVar (Short "v2"); EVar (Short "v3")]])]))] "rev")
                                      :: nsEmpty;
                               sec := nsEmpty |} "v1"
                               (EApp Opapp
                                  [EApp Opapp [EVar (Short "rev"); EVar (Short "v1")];
                                  ECon (Some (Short "[]")) []]))
                             :: (Short "rev",
                                Closure
                                  {|
                                  sev := (Short "rev",
                                         Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                                           [("rev", "v4",
                                            EFun "v3"
                                              (EMat (EVar (Short "v4"))
                                                 [(Pcon (Some (Short "[]")) [], EVar (Short "v3"));
                                                 (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                                                 EApp Opapp
                                                   [EApp Opapp [EVar (Short "rev"); EVar (Short "v1")];
                                                   ECon (Some (Short "::"))
                                                     [EVar (Short "v2"); EVar (Short "v3")]])]))] "rev")
                                         :: nsEmpty;
                                  sec := nsEmpty |} "v1"
                                  (EApp Opapp
                                     [EApp Opapp [EVar (Short "rev"); EVar (Short "v1")];
                                     ECon (Some (Short "[]")) []])) :: nsEmpty;
                      sec := nsEmpty |}
                      [("partition_aux", "v3",
                       EFun "v5"
                         (EFun "v6"
                            (EFun "v4"
                               (EMat (EVar (Short "v5"))
                                  [(Pcon (Some (Short "[]")) [],
                                   ECon None
                                     [EApp Opapp [EVar (Short "rev"); EVar (Short "v6")];
                                     EApp Opapp [EVar (Short "rev"); EVar (Short "v4")]]);
                                  (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                                  EIf (EApp Opapp [EVar (Short "v3"); EVar (Short "v2")])
                                    (EApp Opapp
                                       [EApp Opapp
                                          [EApp Opapp
                                             [EApp Opapp
                                                [EVar (Short "partition_aux"); EVar (Short "v3")];
                                             EVar (Short "v1")];
                                          ECon (Some (Short "::"))
                                            [EVar (Short "v2"); EVar (Short "v6")]];
                                       EVar (Short "v4")])
                                    (EApp Opapp
                                       [EApp Opapp
                                          [EApp Opapp
                                             [EApp Opapp
                                                [EVar (Short "partition_aux"); EVar (Short "v3")];
                                             EVar (Short "v1")]; EVar (Short "v6")];
                                       ECon (Some (Short "::")) [EVar (Short "v2"); EVar (Short "v4")]]))]))))]
                      "partition_aux") :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EFun "v2"
                (EApp Opapp
                   [EApp Opapp
                      [EApp Opapp
                         [EApp Opapp [EVar (Short "partition_aux"); EVar (Short "v1")];
                         EVar (Short "v2")]; ECon (Some (Short "[]")) []];
                   ECon (Some (Short "[]")) []])));
           (Long "List" (Short "filter"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("filter", "v3",
              EFun "v4"
                (EMat (EVar (Short "v4"))
                   [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                   EIf (EApp Opapp [EVar (Short "v3"); EVar (Short "v2")])
                     (ECon (Some (Short "::"))
                        [EVar (Short "v2");
                        EApp Opapp
                          [EApp Opapp [EVar (Short "filter"); EVar (Short "v3")]; EVar (Short "v1")]])
                     (EApp Opapp
                        [EApp Opapp [EVar (Short "filter"); EVar (Short "v3")]; EVar (Short "v1")]))]))]
             "filter");
           (Long "List" (Short "find"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("find", "v3",
              EFun "v4"
                (EMat (EVar (Short "v4"))
                   [(Pcon (Some (Short "[]")) [], ECon (Some (Short "None")) []);
                   (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                   EIf (EApp Opapp [EVar (Short "v3"); EVar (Short "v2")])
                     (ECon (Some (Short "Some")) [EVar (Short "v2")])
                     (EApp Opapp
                        [EApp Opapp [EVar (Short "find"); EVar (Short "v3")]; EVar (Short "v1")]))]))]
             "find");
           (Long "List" (Short "app"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("app", "f",
              EFun "ls"
                (EMat (EVar (Short "ls"))
                   [(Pcon (Some (Short "[]")) [], ECon None []);
                   (Pcon (Some (Short "::")) [Pvar "x"; Pvar "xs"],
                   ELet None (EApp Opapp [EVar (Short "f"); EVar (Short "x")])
                     (EApp Opapp [EApp Opapp [EVar (Short "app"); EVar (Short "f")]; EVar (Short "xs")]))]))]
             "app");
           (Long "List" (Short "mapPartial"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("mapPartial", "v4",
              EFun "v5"
                (EMat (EVar (Short "v5"))
                   [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::")) [Pvar "v3"; Pvar "v2"],
                   EMat (EApp Opapp [EVar (Short "v4"); EVar (Short "v3")])
                     [(Pcon (Some (Short "None")) [],
                      EApp Opapp
                        [EApp Opapp [EVar (Short "mapPartial"); EVar (Short "v4")]; EVar (Short "v2")]);
                     (Pcon (Some (Short "Some")) [Pvar "v1"],
                     ECon (Some (Short "::"))
                       [EVar (Short "v1");
                       EApp Opapp
                         [EApp Opapp [EVar (Short "mapPartial"); EVar (Short "v4")]; EVar (Short "v2")]])])]))]
             "mapPartial");
           (Long "List" (Short "mapi"),
           Closure
             {|
             sev := (Short "mapi",
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("mapi", "v4",
                       EFun "v5"
                         (EFun "v6"
                            (EMat (EVar (Short "v6"))
                               [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                               (Pcon (Some (Short "::")) [Pvar "v3"; Pvar "v2"],
                               ELet (Some "v1")
                                 (EApp Opapp
                                    [EApp Opapp [EVar (Short "v4"); EVar (Short "v5")];
                                    EVar (Short "v3")])
                                 (ECon (Some (Short "::"))
                                    [EVar (Short "v1");
                                    EApp Opapp
                                      [EApp Opapp
                                         [EApp Opapp [EVar (Short "mapi"); EVar (Short "v4")];
                                         EApp (Opn Plus) [EVar (Short "v5"); ELit (IntLit 1)]];
                                      EVar (Short "v2")]]))])))] "mapi") :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EFun "v2"
                (EApp Opapp
                   [EApp Opapp [EApp Opapp [EVar (Short "mapi"); EVar (Short "v1")]; ELit (IntLit 0)];
                   EVar (Short "v2")])));
           (Long "List" (Short "map"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("map", "v4",
              EFun "v5"
                (EMat (EVar (Short "v5"))
                   [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::")) [Pvar "v3"; Pvar "v2"],
                   ELet (Some "v1") (EApp Opapp [EVar (Short "v4"); EVar (Short "v3")])
                     (ECon (Some (Short "::"))
                        [EVar (Short "v1");
                        EApp Opapp
                          [EApp Opapp [EVar (Short "map"); EVar (Short "v4")]; EVar (Short "v2")]]))]))]
             "map");
           (Long "List" (Short "concat"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("concat", "v3",
              EMat (EVar (Short "v3"))
                [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                EApp ListAppend
                  [EVar (Short "v2"); EApp Opapp [EVar (Short "concat"); EVar (Short "v1")]])])]
             "concat");
           (Long "List" (Short "cmp"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("cmp", "v7",
              EFun "v8"
                (EFun "v9"
                   (EMat (EVar (Short "v8"))
                      [(Pcon (Some (Short "[]")) [],
                       EMat (EVar (Short "v9"))
                         [(Pcon (Some (Short "[]")) [], ECon (Some (Short "Equal")) []);
                         (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                         ECon (Some (Short "Less")) [])]);
                      (Pcon (Some (Short "::")) [Pvar "v6"; Pvar "v5"],
                      EMat (EVar (Short "v9"))
                        [(Pcon (Some (Short "[]")) [], ECon (Some (Short "Greater")) []);
                        (Pcon (Some (Short "::")) [Pvar "v4"; Pvar "v3"],
                        EMat
                          (EApp Opapp
                             [EApp Opapp [EVar (Short "v7"); EVar (Short "v6")]; EVar (Short "v4")])
                          [(Pcon (Some (Short "Less")) [], ECon (Some (Short "Less")) []);
                          (Pcon (Some (Short "Equal")) [],
                          EApp Opapp
                            [EApp Opapp
                               [EApp Opapp [EVar (Short "cmp"); EVar (Short "v7")]; EVar (Short "v5")];
                            EVar (Short "v3")]);
                          (Pcon (Some (Short "Greater")) [], ECon (Some (Short "Greater")) [])])])])))]
             "cmp");
           (Long "List" (Short "dropUntil"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("dropUntil", "v3",
              EFun "v4"
                (EMat (EVar (Short "v4"))
                   [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                   EIf (EApp Opapp [EVar (Short "v3"); EVar (Short "v2")])
                     (ECon (Some (Short "::")) [EVar (Short "v2"); EVar (Short "v1")])
                     (EApp Opapp
                        [EApp Opapp [EVar (Short "dropUntil"); EVar (Short "v3")]; EVar (Short "v1")]))]))]
             "dropUntil");
           (Long "List" (Short "takeUntil"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("takeUntil", "v3",
              EFun "v4"
                (EMat (EVar (Short "v4"))
                   [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                   EIf (EApp Opapp [EVar (Short "v3"); EVar (Short "v2")])
                     (ECon (Some (Short "[]")) [])
                     (ECon (Some (Short "::"))
                        [EVar (Short "v2");
                        EApp Opapp
                          [EApp Opapp [EVar (Short "takeUntil"); EVar (Short "v3")]; EVar (Short "v1")]]))]))]
             "takeUntil");
           (Long "List" (Short "drop"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("drop", "v3",
              EFun "v4"
                (EMat (EVar (Short "v3"))
                   [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                   EIf (EApp Equality [EVar (Short "v4"); ELit (IntLit 0)])
                     (ECon (Some (Short "::")) [EVar (Short "v2"); EVar (Short "v1")])
                     (EApp Opapp
                        [EApp Opapp [EVar (Short "drop"); EVar (Short "v1")];
                        ELet (Some "k") (EApp (Opn Minus) [EVar (Short "v4"); ELit (IntLit 1)])
                          (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                             (ELit (IntLit 0)) (EVar (Short "k")))]))]))] "drop");
           (Long "List" (Short "take"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("take", "v3",
              EFun "v4"
                (EMat (EVar (Short "v3"))
                   [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                   (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                   EIf (EApp Equality [EVar (Short "v4"); ELit (IntLit 0)])
                     (ECon (Some (Short "[]")) [])
                     (ECon (Some (Short "::"))
                        [EVar (Short "v2");
                        EApp Opapp
                          [EApp Opapp [EVar (Short "take"); EVar (Short "v1")];
                          ELet (Some "k") (EApp (Opn Minus) [EVar (Short "v4"); ELit (IntLit 1)])
                            (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                               (ELit (IntLit 0)) (EVar (Short "k")))]]))]))] "take");
           (Long "List" (Short "nth"),
           Recclosure
             {|
             sev := (Short "hd",
                    Closure {| sev := nsEmpty; sec := nsEmpty |} "x0"
                      (EMat (EVar (Short "x0"))
                         [(Pcon (Some (Short "[]")) [], ERaise (ECon (Some (Short "Bind")) []));
                         (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"], EVar (Short "v2"))]))
                    :: (Short "tl",
                       Closure {| sev := nsEmpty; sec := nsEmpty |} "v3"
                         (EMat (EVar (Short "v3"))
                            [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                            (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"], EVar (Short "v1"))]))
                       :: nsEmpty;
             sec := nsEmpty |}
             [("nth", "v1",
              EFun "v2"
                (EIf (EApp Equality [EVar (Short "v2"); ELit (IntLit 0)])
                   (EApp Opapp [EVar (Short "hd"); EVar (Short "v1")])
                   (EApp Opapp
                      [EApp Opapp
                         [EVar (Short "nth"); EApp Opapp [EVar (Short "tl"); EVar (Short "v1")]];
                      ELet (Some "k") (EApp (Opn Minus) [EVar (Short "v2"); ELit (IntLit 1)])
                        (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                           (ELit (IntLit 0)) (EVar (Short "k")))])))] "nth");
           (Long "List" (Short "getItem"),
           Closure
             {|
             sev := nsEmpty;
             sec := (Short "None", (0%nat, TypeStamp "None" 0))
                    :: (Short "Some", (1%nat, TypeStamp "Some" 0)) :: nsEmpty |} "v3"
             (EMat (EVar (Short "v3"))
                [(Pcon (Some (Short "[]")) [], ECon (Some (Short "None")) []);
                (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                ECon (Some (Short "Some")) [ECon None [EVar (Short "v2"); EVar (Short "v1")]])]));
           (Long "List" (Short "last"),
           Recclosure {| sev := nsEmpty; sec := nsEmpty |}
             [("last", "x0",
              EMat (EVar (Short "x0"))
                [(Pcon (Some (Short "[]")) [], ERaise (ECon (Some (Short "Bind")) []));
                (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                EIf (EApp Equality [EVar (Short "v1"); ECon (Some (Short "[]")) []])
                  (EVar (Short "v2")) (EApp Opapp [EVar (Short "last"); EVar (Short "v1")]))])] "last");
           (Long "List" (Short "tl"),
           Closure {| sev := nsEmpty; sec := nsEmpty |} "v3"
             (EMat (EVar (Short "v3"))
                [(Pcon (Some (Short "[]")) [], ECon (Some (Short "[]")) []);
                (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"], EVar (Short "v1"))]));
           (Long "List" (Short "hd"),
           Closure {| sev := nsEmpty; sec := nsEmpty |} "x0"
             (EMat (EVar (Short "x0"))
                [(Pcon (Some (Short "[]")) [], ERaise (ECon (Some (Short "Bind")) []));
                (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"], EVar (Short "v2"))]));
           (Long "List" (Short "@"),
           Closure {| sev := nsEmpty; sec := nsEmpty |} "v1"
             (EFun "v2" (EApp ListAppend [EVar (Short "v1"); EVar (Short "v2")])));
           (Long "List" (Short "rev"),
           Closure
             {|
             sev := (Short "rev",
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("rev", "v4",
                       EFun "v3"
                         (EMat (EVar (Short "v4"))
                            [(Pcon (Some (Short "[]")) [], EVar (Short "v3"));
                            (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                            EApp Opapp
                              [EApp Opapp [EVar (Short "rev"); EVar (Short "v1")];
                              ECon (Some (Short "::")) [EVar (Short "v2"); EVar (Short "v3")]])]))]
                      "rev") :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EApp Opapp
                [EApp Opapp [EVar (Short "rev"); EVar (Short "v1")]; ECon (Some (Short "[]")) []]));
           (Long "List" (Short "length"),
           Closure
             {|
             sev := (Short "length_aux",
                    Recclosure {| sev := nsEmpty; sec := nsEmpty |}
                      [("length_aux", "v3",
                       EFun "v4"
                         (EMat (EVar (Short "v3"))
                            [(Pcon (Some (Short "[]")) [], EVar (Short "v4"));
                            (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                            EApp Opapp
                              [EApp Opapp [EVar (Short "length_aux"); EVar (Short "v1")];
                              EApp (Opn Plus) [EVar (Short "v4"); ELit (IntLit 1)]])]))] "length_aux")
                    :: nsEmpty;
             sec := nsEmpty |} "v1"
             (EApp Opapp [EApp Opapp [EVar (Short "length_aux"); EVar (Short "v1")]; ELit (IntLit 0)]));
           (Long "List" (Short "null"),
           Closure {| sev := nsEmpty; sec := nsEmpty |} "v3"
             (EMat (EVar (Short "v3"))
                [(Pcon (Some (Short "[]")) [], EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)]);
                (Pcon (Some (Short "::")) [Pvar "v2"; Pvar "v1"],
                EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)])]));
           (Long "Option" (Short "compare"),
           Closure
             {|
             sev := [];
             sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Equal", (0%nat, TypeStamp "Equal" 1));
                    (Short "Some", (1%nat, TypeStamp "Some" 0));
                    (Short "Less", (0%nat, TypeStamp "Less" 1));
                    (Short "Some", (1%nat, TypeStamp "Some" 0));
                    (Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Greater", (0%nat, TypeStamp "Greater" 1));
                    (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v4"
             (EFun "v5"
                (EFun "v6"
                   (EMat (EVar (Short "v5"))
                      [(Pcon (Some (Short "None")) [],
                       EMat (EVar (Short "v6"))
                         [(Pcon (Some (Short "None")) [], ECon (Some (Short "Equal")) []);
                         (Pcon (Some (Short "Some")) [Pvar "v1"], ECon (Some (Short "Less")) [])]);
                      (Pcon (Some (Short "Some")) [Pvar "v3"],
                      EMat (EVar (Short "v6"))
                        [(Pcon (Some (Short "None")) [], ECon (Some (Short "Greater")) []);
                        (Pcon (Some (Short "Some")) [Pvar "v2"],
                        EApp Opapp
                          [EApp Opapp [EVar (Short "v4"); EVar (Short "v3")]; EVar (Short "v2")])])]))));
           (Long "Option" (Short "map2"),
           Closure
             {|
             sev := [(Short "isSome",
                     Closure
                       {|
                       sev := [];
                       sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                              (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v2"
                       (EMat (EVar (Short "v2"))
                          [(Pcon (Some (Short "None")) [],
                           EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]);
                          (Pcon (Some (Short "Some")) [Pvar "v1"],
                          EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)])]));
                    (Short "isSome",
                    Closure
                      {|
                      sev := [];
                      sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                             (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v2"
                      (EMat (EVar (Short "v2"))
                         [(Pcon (Some (Short "None")) [],
                          EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]);
                         (Pcon (Some (Short "Some")) [Pvar "v1"],
                         EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)])]));
                    (Short "valOf",
                    Closure
                      {|
                      sev := [];
                      sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                             (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "x0"
                      (EMat (EVar (Short "x0"))
                         [(Pcon (Some (Short "None")) [], ERaise (ECon (Some (Short "Bind")) []));
                         (Pcon (Some (Short "Some")) [Pvar "v1"], EVar (Short "v1"))]));
                    (Short "valOf",
                    Closure
                      {|
                      sev := [];
                      sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                             (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "x0"
                      (EMat (EVar (Short "x0"))
                         [(Pcon (Some (Short "None")) [], ERaise (ECon (Some (Short "Bind")) []));
                         (Pcon (Some (Short "Some")) [Pvar "v1"], EVar (Short "v1"))]))];
             sec := [(Short "Some", (1%nat, TypeStamp "Some" 0));
                    (Short "None", (0%nat, TypeStamp "None" 0))] |} "v1"
             (EFun "v2"
                (EFun "v3"
                   (EIf
                      (ELog And (EApp Opapp [EVar (Short "isSome"); EVar (Short "v2")])
                         (EApp Opapp [EVar (Short "isSome"); EVar (Short "v3")]))
                      (ECon (Some (Short "Some"))
                         [EApp Opapp
                            [EApp Opapp
                               [EVar (Short "v1");
                               EApp Opapp [EVar (Short "valOf"); EVar (Short "v2")]];
                            EApp Opapp [EVar (Short "valOf"); EVar (Short "v3")]]])
                      (ECon (Some (Short "None")) [])))));
           (Long "Option" (Short "isNone"),
           Closure
             {|
             sev := [];
             sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v2"
             (EMat (EVar (Short "v2"))
                [(Pcon (Some (Short "None")) [], EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)]);
                (Pcon (Some (Short "Some")) [Pvar "v1"],
                EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)])]));
           (Long "Option" (Short "composePartial"),
           Closure
             {|
             sev := [];
             sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v3"
             (EFun "v4"
                (EFun "v2"
                   (EMat (EApp Opapp [EVar (Short "v4"); EVar (Short "v2")])
                      [(Pcon (Some (Short "None")) [], ECon (Some (Short "None")) []);
                      (Pcon (Some (Short "Some")) [Pvar "v1"],
                      EApp Opapp [EVar (Short "v3"); EVar (Short "v1")])]))));
           (Long "Option" (Short "compose"),
           Closure
             {|
             sev := [];
             sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v3"
             (EFun "v4"
                (EFun "v2"
                   (EMat (EApp Opapp [EVar (Short "v4"); EVar (Short "v2")])
                      [(Pcon (Some (Short "None")) [], ECon (Some (Short "None")) []);
                      (Pcon (Some (Short "Some")) [Pvar "v1"],
                      ECon (Some (Short "Some")) [EApp Opapp [EVar (Short "v3"); EVar (Short "v1")]])]))));
           (Long "Option" (Short "mapPartial"),
           Closure
             {|
             sev := [];
             sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v2"
             (EFun "v3"
                (EMat (EVar (Short "v3"))
                   [(Pcon (Some (Short "None")) [], ECon (Some (Short "None")) []);
                   (Pcon (Some (Short "Some")) [Pvar "v1"],
                   EApp Opapp [EVar (Short "v2"); EVar (Short "v1")])])));
           (Long "Option" (Short "map"),
           Closure
             {|
             sev := [];
             sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v2"
             (EFun "v3"
                (EMat (EVar (Short "v3"))
                   [(Pcon (Some (Short "None")) [], ECon (Some (Short "None")) []);
                   (Pcon (Some (Short "Some")) [Pvar "v1"],
                   ECon (Some (Short "Some")) [EApp Opapp [EVar (Short "v2"); EVar (Short "v1")]])])));
           (Long "Option" (Short "join"),
           Closure
             {|
             sev := [];
             sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v2"
             (EMat (EVar (Short "v2"))
                [(Pcon (Some (Short "None")) [], ECon (Some (Short "None")) []);
                (Pcon (Some (Short "Some")) [Pvar "v1"], EVar (Short "v1"))]));
           (Long "Option" (Short "valOf"),
           Closure
             {|
             sev := [];
             sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "x0"
             (EMat (EVar (Short "x0"))
                [(Pcon (Some (Short "None")) [], ERaise (ECon (Some (Short "Bind")) []));
                (Pcon (Some (Short "Some")) [Pvar "v1"], EVar (Short "v1"))]));
           (Long "Option" (Short "isSome"),
           Closure
             {|
             sev := [];
             sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v2"
             (EMat (EVar (Short "v2"))
                [(Pcon (Some (Short "None")) [], EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]);
                (Pcon (Some (Short "Some")) [Pvar "v1"],
                EApp (Opb Leq) [ELit (IntLit 0); ELit (IntLit 0)])]));
           (Long "Option" (Short "getOpt"),
           Closure
             {|
             sev := [];
             sec := [(Short "None", (0%nat, TypeStamp "None" 0));
                    (Short "Some", (1%nat, TypeStamp "Some" 0))] |} "v3"
             (EFun "v2"
                (EMat (EVar (Short "v3"))
                   [(Pcon (Some (Short "None")) [], EVar (Short "v2"));
                   (Pcon (Some (Short "Some")) [Pvar "v1"], EVar (Short "v1"))])));
           (Long "Runtime" (Short "abort"),
           Recclosure
             {|
             sev := [(Short "exit",
                     Recclosure {| sev := []; sec := [] |}
                       [("exit", "i",
                        ELet (Some "y") (EApp (WordFromInt W8) [EVar (Short "i")])
                          (ELet (Some "x") (EApp Aw8alloc [ELit (IntLit 1); EVar (Short "y")])
                             (EApp (FFI "exit") [ELit (StrLit ""); EVar (Short "x")])))] "exit")];
             sec := [] |}
             [("abort", "u",
              EMat (EVar (Short "u"))
                [(Pcon None [], EApp Opapp [EVar (Short "exit"); ELit (IntLit 1)])])] "abort");
           (Long "Runtime" (Short "exit"),
           Recclosure {| sev := []; sec := [] |}
             [("exit", "i",
              ELet (Some "y") (EApp (WordFromInt W8) [EVar (Short "i")])
                (ELet (Some "x") (EApp Aw8alloc [ELit (IntLit 1); EVar (Short "y")])
                   (EApp (FFI "exit") [ELit (StrLit ""); EVar (Short "x")])))] "exit");
           (Long "Runtime" (Short "debugMsg"),
           Closure {| sev := []; sec := [] |} "v1"
             (EApp (FFI "")
                [EVar (Short "v1"); EApp Aw8alloc [ELit (IntLit 0); ELit (Word8Lit (nat_to_word 8 0))]]));
           (Long "Runtime" (Short "fail"),
           Closure {| sev := []; sec := [] |} "v1"
             (EMat (EVar (Short "v1"))
                [(Pcon None [],
                 ELet (Some "a") (EVar (Short "v1"))
                   (ELet (Some "n") (ELit (StrLit "18446744073709551616"))
                      (ELet None (EApp Aalloc [EVar (Short "n"); EVar (Short "n")]) (EVar (Short "a")))))]));
           (Long "Runtime" (Short "fullGC"),
           Closure {| sev := []; sec := [] |} "v1"
             (EMat (EVar (Short "v1"))
                [(Pcon None [], EApp ConfigGC [ELit (IntLit 0); ELit (IntLit 0)])]));
           (Short "repeat",
           Recclosure {| sev := []; sec := [] |}
             [("repeat", "f",
              EFun "x"
                (ELet (Some "a") (EApp Opapp [EVar (Short "f"); EVar (Short "x")])
                   (EApp Opapp [EApp Opapp [EVar (Short "repeat"); EVar (Short "f")]; EVar (Short "a")])))]
             "repeat");
           (Short "least",
           Closure
             {|
             sev := [(Short "while",
                     Recclosure {| sev := []; sec := [] |}
                       [("while", "v1",
                        EFun "v2"
                          (EFun "v3"
                             (EIf (EApp Opapp [EVar (Short "v1"); EVar (Short "v3")])
                                (EApp Opapp
                                   [EApp Opapp
                                      [EApp Opapp [EVar (Short "while"); EVar (Short "v1")];
                                      EVar (Short "v2")];
                                   EApp Opapp [EVar (Short "v2"); EVar (Short "v3")]])
                                (EVar (Short "v3")))))] "while")];
             sec := [] |} "v3"
             (EApp Opapp
                [EApp Opapp
                   [EApp Opapp
                      [EVar (Short "while");
                      EFun "v1"
                        (EApp Equality
                           [EApp Opapp [EVar (Short "v3"); EVar (Short "v1")];
                           EApp (Opb Lt) [ELit (IntLit 0); ELit (IntLit 0)]])];
                   EFun "v2" (EApp (Opn Plus) [EVar (Short "v2"); ELit (IntLit 1)])];
                ELit (IntLit 0)]));
           (Short "owhile",
           Recclosure {| sev := []; sec := [] |}
             [("owhile", "v1",
              EFun "v2"
                (EFun "v3"
                   (EIf (EApp Opapp [EVar (Short "v1"); EVar (Short "v3")])
                      (EApp Opapp
                         [EApp Opapp
                            [EApp Opapp [EVar (Short "owhile"); EVar (Short "v1")]; EVar (Short "v2")];
                         EApp Opapp [EVar (Short "v2"); EVar (Short "v3")]])
                      (ECon (Some (Short "Some")) [EVar (Short "v3")]))))] "owhile");
           (Short "while",
           Recclosure {| sev := []; sec := [] |}
             [("while", "v1",
              EFun "v2"
                (EFun "v3"
                   (EIf (EApp Opapp [EVar (Short "v1"); EVar (Short "v3")])
                      (EApp Opapp
                         [EApp Opapp
                            [EApp Opapp [EVar (Short "while"); EVar (Short "v1")]; EVar (Short "v2")];
                         EApp Opapp [EVar (Short "v2"); EVar (Short "v3")]])
                      (EVar (Short "v3")))))] "while");
           (Short "pre",
           Closure {| sev := []; sec := [] |} "v1"
             (ELet (Some "k") (EApp (Opn Minus) [EVar (Short "v1"); ELit (IntLit 1)])
                (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)]) (ELit (IntLit 0))
                   (EVar (Short "k")))));
           (Short "abs_diff",
           Closure {| sev := []; sec := [] |} "v2"
             (EFun "v1"
                (EIf (EApp (Opb Lt) [EVar (Short "v2"); EVar (Short "v1")])
                   (ELet (Some "k") (EApp (Opn Minus) [EVar (Short "v1"); EVar (Short "v2")])
                      (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                         (ELit (IntLit 0)) (EVar (Short "k"))))
                   (ELet (Some "k") (EApp (Opn Minus) [EVar (Short "v2"); EVar (Short "v1")])
                      (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                         (ELit (IntLit 0)) (EVar (Short "k")))))));
           (Short "funpow",
           Recclosure {| sev := []; sec := [] |}
             [("funpow", "v1",
              EFun "v2"
                (EFun "v3"
                   (EIf (EApp Equality [EVar (Short "v2"); ELit (IntLit 0)])
                      (EVar (Short "v3"))
                      (EApp Opapp
                         [EApp Opapp
                            [EApp Opapp [EVar (Short "funpow"); EVar (Short "v1")];
                            ELet (Some "k") (EApp (Opn Minus) [EVar (Short "v2"); ELit (IntLit 1)])
                              (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                 (ELit (IntLit 0)) (EVar (Short "k")))];
                         EApp Opapp [EVar (Short "v1"); EVar (Short "v3")]]))))] "funpow");
           (Short "odd",
           Closure {| sev := []; sec := [] |} "v1"
             (EApp (Opb Lt) [ELit (IntLit 0); EApp (Opn Modulo) [EVar (Short "v1"); ELit (IntLit 2)]]));
           (Short "even",
           Closure {| sev := []; sec := [] |} "v1"
             (EApp Equality [EApp (Opn Modulo) [EVar (Short "v1"); ELit (IntLit 2)]; ELit (IntLit 0)]));
           (Short "max",
           Closure {| sev := []; sec := [] |} "v1"
             (EFun "v2"
                (EIf (EApp (Opb Lt) [EVar (Short "v1"); EVar (Short "v2")])
                   (EVar (Short "v2")) (EVar (Short "v1")))));
           (Short "min",
           Closure {| sev := []; sec := [] |} "v1"
             (EFun "v2"
                (EIf (EApp (Opb Lt) [EVar (Short "v1"); EVar (Short "v2")])
                   (EVar (Short "v1")) (EVar (Short "v2")))));
           (Short "exp",
           Closure
             {|
             sev := [(Short "exp",
                     Recclosure {| sev := []; sec := [] |}
                       [("exp", "v2",
                        EFun "v3"
                          (EFun "v1"
                             (EIf (EApp Equality [EVar (Short "v3"); ELit (IntLit 0)])
                                (EVar (Short "v1"))
                                (EApp Opapp
                                   [EApp Opapp
                                      [EApp Opapp [EVar (Short "exp"); EVar (Short "v2")];
                                      ELet (Some "k")
                                        (EApp (Opn Minus) [EVar (Short "v3"); ELit (IntLit 1)])
                                        (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                           (ELit (IntLit 0)) (EVar (Short "k")))];
                                   EApp (Opn Times) [EVar (Short "v2"); EVar (Short "v1")]]))))] "exp")];
             sec := [] |} "v1"
             (EFun "v2"
                (EApp Opapp
                   [EApp Opapp [EApp Opapp [EVar (Short "exp"); EVar (Short "v1")]; EVar (Short "v2")];
                   ELit (IntLit 1)])));
           (Short "exp",
           Recclosure {| sev := []; sec := [] |}
             [("exp", "v2",
              EFun "v3"
                (EFun "v1"
                   (EIf (EApp Equality [EVar (Short "v3"); ELit (IntLit 0)])
                      (EVar (Short "v1"))
                      (EApp Opapp
                         [EApp Opapp
                            [EApp Opapp [EVar (Short "exp"); EVar (Short "v2")];
                            ELet (Some "k") (EApp (Opn Minus) [EVar (Short "v3"); ELit (IntLit 1)])
                              (EIf (EApp (Opb Lt) [EVar (Short "k"); ELit (IntLit 0)])
                                 (ELit (IntLit 0)) (EVar (Short "k")))];
                         EApp (Opn Times) [EVar (Short "v2"); EVar (Short "v1")]]))))] "exp");
           (Short "update",
           Closure {| sev := []; sec := [] |} "v3"
             (EFun "v4"
                (EFun "v2"
                   (EFun "v1"
                      (EIf (EApp Equality [EVar (Short "v3"); EVar (Short "v1")])
                         (EVar (Short "v4")) (EApp Opapp [EVar (Short "v2"); EVar (Short "v1")]))))));
           (Short "const", Closure {| sev := []; sec := [] |} "v2" (EFun "v1" (EVar (Short "v2"))));
           (Short "flip",
           Closure {| sev := []; sec := [] |} "v3"
             (EFun "v2"
                (EFun "v1"
                   (EApp Opapp [EApp Opapp [EVar (Short "v3"); EVar (Short "v1")]; EVar (Short "v2")]))));
           (Short "id", Closure {| sev := []; sec := [] |} "v1" (EVar (Short "v1")));
           (Short "o",
           Closure {| sev := []; sec := [] |} "v2"
             (EFun "v3"
                (EFun "v1"
                   (EApp Opapp [EVar (Short "v2"); EApp Opapp [EVar (Short "v3"); EVar (Short "v1")]]))));
           (Short "uncurry",
           Closure
             {|
             sev := [(Short "fst",
                     Closure {| sev := []; sec := [] |} "v3"
                       (EMat (EVar (Short "v3"))
                          [(Pcon None [Pvar "v2"; Pvar "v1"], EVar (Short "v2"))]));
                    (Short "snd",
                    Closure {| sev := []; sec := [] |} "v3"
                      (EMat (EVar (Short "v3")) [(Pcon None [Pvar "v2"; Pvar "v1"], EVar (Short "v1"))]))];
             sec := [] |} "v1"
             (EFun "v2"
                (EApp Opapp
                   [EApp Opapp [EVar (Short "v1"); EApp Opapp [EVar (Short "fst"); EVar (Short "v2")]];
                   EApp Opapp [EVar (Short "snd"); EVar (Short "v2")]])));
           (Short "curry",
           Closure {| sev := []; sec := [] |} "v1"
             (EFun "v2"
                (EFun "v3"
                   (EApp Opapp [EVar (Short "v1"); ECon None [EVar (Short "v2"); EVar (Short "v3")]]))));
           (Short "snd",
           Closure {| sev := []; sec := [] |} "v3"
             (EMat (EVar (Short "v3")) [(Pcon None [Pvar "v2"; Pvar "v1"], EVar (Short "v1"))]));
           (Short "fst",
           Closure {| sev := []; sec := [] |} "v3"
             (EMat (EVar (Short "v3")) [(Pcon None [Pvar "v2"; Pvar "v1"], EVar (Short "v2"))]))];
    sec := [(Short "Inl", (1%nat, TypeStamp "Inl" 2)); (Short "Inr", (1%nat, TypeStamp "Inr" 2));
           (Short "Less", (0%nat, TypeStamp "Less" 1)); (Short "Equal", (0%nat, TypeStamp "Equal" 1));
           (Short "Greater", (0%nat, TypeStamp "Greater" 1));
           (Short "None", (0%nat, TypeStamp "None" 0)); (Short "Some", (1%nat, TypeStamp "Some" 0))] |}.
