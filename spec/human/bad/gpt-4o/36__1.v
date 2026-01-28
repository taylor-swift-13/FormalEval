Require Import Coq.Arith.Arith Coq.Bool.Bool Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Inductive digit_7_count_rel : nat -> nat -> Prop :=
| d7c_zero : digit_7_count_rel 0 0
| d7c_mod10_7 : forall n c,
    n mod 10 = 7 ->
    digit_7_count_rel (n / 10) c ->
    digit_7_count_rel n (S c)
| d7c_mod10_other : forall n c,
    n mod 10 <> 7 ->
    digit_7_count_rel (n / 10) c ->
    digit_7_count_rel n c.

Inductive fizz_buzz_rel : nat -> nat -> Prop :=
| fbz_zero : fizz_buzz_rel 0 0
| fbz_next_div : forall n acc c,
    fizz_buzz_rel n acc ->
    (n mod 11 = 0 \/ n mod 13 = 0) ->
    digit_7_count_rel n c ->
    fizz_buzz_rel (S n) (acc + c)
| fbz_next_nodiv : forall n acc,
    fizz_buzz_rel n acc ->
    ~(n mod 11 = 0 \/ n mod 13 = 0) ->
    fizz_buzz_rel (S n) acc.

Definition problem_36_pre (n : nat) : Prop := True.

Definition problem_36_spec (n : nat) (output : nat) : Prop :=
  fizz_buzz_rel n output.

Example fizz_buzz_50 : problem_36_spec 50 0.
Proof.
  unfold problem_36_spec.
  apply fbz_next_nodiv with (acc := 0).
  - (* for n = 49 *)
    assert (49 mod 11 <> 0 /\ 49 mod 13 <> 0) by (split; lia).
    apply fbz_next_nodiv with (acc := 0).
    + (* for n = 48 *)
      assert (48 mod 11 <> 0 /\ 48 mod 13 <> 0) by (split; lia).
      apply fbz_next_nodiv with (acc := 0).
      * (* for n = 47 *)
        assert (47 mod 11 <> 0 /\ 47 mod 13 <> 0) by (split; lia).
        apply fbz_next_nodiv with (acc := 0).
        -- (* for n = 46 *)
           assert (46 mod 11 <> 0 /\ 46 mod 13 <> 0) by (split; lia).
           apply fbz_next_nodiv with (acc := 0).
           ++ (* for n = 45 *)
              assert (45 mod 11 <> 0 /\ 45 mod 13 <> 0) by (split; lia).
              apply fbz_next_nodiv with (acc := 0).
              ** (* for n = 44 *)
                 assert (44 mod 11 = 0) by lia.
                 apply fbz_next_div with (c := 0).
                 --- (* for n = 43 *)
                     assert (43 mod 11 <> 0 /\ 43 mod 13 <> 0) by (split; lia).
                     apply fbz_next_nodiv with (acc := 0).
                     +++ (* for n = 42 *)
                         assert (42 mod 11 <> 0 /\ 42 mod 13 <> 0) by (split; lia).
                         apply fbz_next_nodiv with (acc := 0).
                         ++++ (* for n = 41 *)
                              assert (41 mod 11 <> 0 /\ 41 mod 13 <> 0) by (split; lia).
                              apply fbz_next_nodiv with (acc := 0).
                              ---- (* for n = 40 *)
                                   assert (40 mod 11 <> 0 /\ 40 mod 13 <> 0) by (split; lia).
                                   apply fbz_next_nodiv with (acc := 0).
                                   ++++ (* for n = 39 *)
                                        assert (39 mod 13 = 0) by lia.
                                        apply fbz_next_div with (c := 0).
                                        ---- (* for n = 38 *)
                                             assert (38 mod 11 <> 0 /\ 38 mod 13 <> 0) by (split; lia).
                                             apply fbz_next_nodiv with (acc := 0).
                                             ++++ (* for n = 37 *)
                                                  assert (37 mod 11 <> 0 /\ 37 mod 13 <> 0) by (split; lia).
                                                  apply fbz_next_nodiv with (acc := 0).
                                                  ---- (* for n = 36 *)
                                                       assert (36 mod 11 <> 0 /\ 36 mod 13 <> 0) by (split; lia).
                                                       apply fbz_next_nodiv with (acc := 0).
                                                       ++++ (* for n = 35 *)
                                                            assert (35 mod 11 <> 0 /\ 35 mod 13 <> 0) by (split; lia).
                                                            apply fbz_next_nodiv with (acc := 0).
                                                            ---- (* for n = 34 *)
                                                                 assert (34 mod 11 <> 0 /\ 34 mod 13 <> 0) by (split; lia).
                                                                 apply fbz_next_nodiv with (acc := 0).
                                                                 ++++ (* for n = 33 *)
                                                                      assert (33 mod 11 = 0) by lia.
                                                                      apply fbz_next_div with (c := 0).
                                                                      ---- (* for n = 32 *)
                                                                           assert (32 mod 11 <> 0 /\ 32 mod 13 <> 0) by (split; lia).
                                                                           apply fbz_next_nodiv with (acc := 0).
                                                                           ++++ (* for n = 31 *)
                                                                                assert (31 mod 11 <> 0 /\ 31 mod 13 <> 0) by (split; lia).
                                                                                apply fbz_next_nodiv with (acc := 0).
                                                                                ---- (* for n = 30 *)
                                                                                     assert (30 mod 11 <> 0 /\ 30 mod 13 <> 0) by (split; lia).
                                                                                     apply fbz_next_nodiv with (acc := 0).
                                                                                     ++++ (* for n = 29 *)
                                                                                          assert (29 mod 11 <> 0 /\ 29 mod 13 <> 0) by (split; lia).
                                                                                          apply fbz_next_nodiv with (acc := 0).
                                                                                          ---- (* for n = 28 *)
                                                                                               assert (28 mod 11 <> 0 /\ 28 mod 13 <> 0) by (split; lia).
                                                                                               apply fbz_next_nodiv with (acc := 0).
                                                                                               ++++ (* for n = 27 *)
                                                                                                    assert (27 mod 11 <> 0 /\ 27 mod 13 <> 0) by (split; lia).
                                                                                                    apply fbz_next_nodiv with (acc := 0).
                                                                                                    ---- (* for n = 26 *)
                                                                                                         assert (26 mod 13 = 0) by lia.
                                                                                                         apply fbz_next_div with (c := 0).
                                                                                                         ++++ (* for n = 25 *)
                                                                                                              assert (25 mod 11 <> 0 /\ 25 mod 13 <> 0) by (split; lia).
                                                                                                              apply fbz_next_nodiv with (acc := 0).
                                                                                                              ---- (* for n = 24 *)
                                                                                                                   assert (24 mod 11 <> 0 /\ 24 mod 13 <> 0) by (split; lia).
                                                                                                                   apply fbz_next_nodiv with (acc := 0).
                                                                                                                   ++++ (* for n = 23 *)
                                                                                                                        assert (23 mod 11 <> 0 /\ 23 mod 13 <> 0) by (split; lia).
                                                                                                                        apply fbz_next_nodiv with (acc := 0).
                                                                                                                        ---- (* for n = 22 *)
                                                                                                                             assert (22 mod 11 = 0) by lia.
                                                                                                                             apply fbz_next_div with (c := 0).
                                                                                                                             ++++ (* for n = 21 *)
                                                                                                                                  assert (21 mod 11 <> 0 /\ 21 mod 13 <> 0) by (split; lia).
                                                                                                                                  apply fbz_next_nodiv with (acc := 0).
                                                                                                                                  ---- (* for n = 20 *)
                                                                                                                                       assert (20 mod 11 <> 0 /\ 20 mod 13 <> 0) by (split; lia).
                                                                                                                                       apply fbz_next_nodiv with (acc := 0).
                                                                                                                                       ++++ (* for n = 19 *)
                                                                                                                                            assert (19 mod 11 <> 0 /\ 19 mod 13 <> 0) by (split; lia).
                                                                                                                                            apply fbz_next_nodiv with (acc := 0).
                                                                                                                                            ---- (* for n = 18 *)
                                                                                                                                                 assert (18 mod 11 <> 0 /\ 18 mod 13 <> 0) by (split; lia).
                                                                                                                                                 apply fbz_next_nodiv with (acc := 0).
                                                                                                                                                 ++++ (* for n = 17 *)
                                                                                                                                                      assert (17 mod 11 <> 0 /\ 17 mod 13 <> 0) by (split; lia).
                                                                                                                                                      apply fbz_next_nodiv with (acc := 0).
                                                                                                                                                      ---- (* for n = 16 *)
                                                                                                                                                           assert (16 mod 11 <> 0 /\ 16 mod 13 <> 0) by (split; lia).
                                                                                                                                                           apply fbz_next_nodiv with (acc := 0).
                                                                                                                                                           ++++ (* for n = 15 *)
                                                                                                                                                                assert (15 mod 11 <> 0 /\ 15 mod 13 <> 0) by (split; lia).
                                                                                                                                                                apply fbz_next_nodiv with (acc := 0).
                                                                                                                                                                ---- (* for n = 14 *)
                                                                                                                                                                     assert (14 mod 11 <> 0 /\ 14 mod 13 <> 0) by (split; lia).
                                                                                                                                                                     apply fbz_next_nodiv with (acc := 0).
                                                                                                                                                                     ++++ (* for n = 13 *)
                                                                                                                                                                          assert (13 mod 13 = 0) by lia.
                                                                                                                                                                          apply fbz_next_div with (c := 0).
                                                                                                                                                                          ---- (* for n = 12 *)
                                                                                                                                                                               assert (12 mod 11 <> 0 /\ 12 mod 13 <> 0) by (split; lia).
                                                                                                                                                                               apply fbz_next_nodiv with (acc := 0).
                                                                                                                                                                               ++++ (* for n = 11 *)
                                                                                                                                                                                    assert (11 mod 11 = 0) by lia.
                                                                                                                                                                                    apply fbz_next_div with (c := 0).
                                                                                                                                                                                    ---- (* for n = 10 *)
                                                                                                                                                                                         assert (10 mod 11 <> 0 /\ 10 mod 13 <> 0) by (split; lia).
                                                                                                                                                                                         apply fbz_next_nodiv with (acc := 0).
                                                                                                                                                                                         ++++ (* for n = 9 *)
                                                                                                                                                                                              assert (9 mod 11 <> 0 /\ 9 mod 13 <> 0) by (split; lia).
                                                                                                                                                                                              apply fbz_next_nodiv with (acc := 0).
                                                                                                                                                                                              ---- (* for n = 8 *)
                                                                                                                                                                                                   assert (8 mod 11 <> 0 /\ 8 mod 13 <> 0) by (split; lia).
                                                                                                                                                                                                   apply fbz_next_nodiv with (acc := 0).
                                                                                                                                                                                                   ++++ (* for n = 7 *)
                                                                                                                                                                                                        assert (7 mod 11 <> 0 /\ 7 mod 13 <> 0) by (split; lia).
                                                                                                                                                                                                        apply fbz_next_nodiv with (acc := 0).
                                                                                                                                                                                                        ---- (* for n = 6 *)
                                                                                                                                                                                                             assert (6 mod 11 <> 0 /\ 6 mod 13 <> 0) by (split; lia).
                                                                                                                                                                                                             apply fbz_next_nodiv with (acc := 0).
                                                                                                                                                                                                             ++++ (* for n = 5 *)
                                                                                                                                                                                                                  assert (5 mod 11 <> 0 /\ 5 mod 13 <> 0) by (split; lia).
                                                                                                                                                                                                                  apply fbz_next_nodiv with (acc := 0).
                                                                                                                                                                                                                  ---- (* for n = 4 *)
                                                                                                                                                                                                                       assert (4 mod 11 <> 0 /\ 4 mod 13 <> 0) by (split; lia).
                                                                                                                                                                                                                       apply fbz_next_nodiv with (acc := 0).
                                                                                                                                                                                                                       ++++ (* for n = 3 *)
                                                                                                                                                                                                                            assert (3 mod 11 <> 0 /\ 3 mod 13 <> 0) by (split; lia).
                                                                                                                                                                                                                            apply fbz_next_nodiv with (acc := 0).
                                                                                                                                                                                                                            ---- (* for n = 2 *)
                                                                                                                                                                                                                                 assert (2 mod 11 <> 0 /\ 2 mod 13 <> 0) by (split; lia).
                                                                                                                                                                                                                                 apply fbz_next_nodiv with (acc := 0).
                                                                                                                                                                                                                                 ++++ (* for n = 1 *)
                                                                                                                                                                                                                                      assert (1 mod 11 <> 0 /\ 1 mod 13 <> 0) by (split; lia).
                                                                                                                                                                                                                                      apply fbz_next_nodiv with (acc := 0).
                                                                                                                                                                                                                                      ---- (* for n = 0 *)
                                                                                                                                                                                                                                           apply fbz_zero.
                                                                                                                                                                                                                                           lia.
                                                                                                                                                                                                                                 lia.
                                                                                                                                                                                                                            lia.
                                                                                                                                                                                                                       lia.
                                                                                                                                                                                                                  lia.
                                                                                                                                                                                                             lia.
                                                                                                                                                                                                        lia.
                                                                                                                                                                                                   lia.
                                                                                                                                                                                              lia.
                                                                                                                                                                                         lia.
                                                                                                                                                                                    lia.
                                                                                                                                                                               lia.
                                                                                                                                                                          lia.
                                                                                                                                                                     lia.
                                                                                                                                                                lia.
                                                                                                                                                           lia.
                                                                                                                                                      lia.
                                                                                                                                                 lia.
                                                                                                                                            lia.
                                                                                                                                       lia.
                                                                                                                                  lia.
                                                                                                                             lia.
                                                                                                                        lia.
                                                                                                                   lia.
                                                                                                              lia.
                                                                                                         lia.
                                                                                                    lia.
                                                                                               lia.
                                                                                          lia.
                                                                                     lia.
                                                                                lia.
                                                                           lia.
                                                                      lia.
                                                                 lia.
                                                            lia.
                                                       lia.
                                                  lia.
                                             lia.
                                        lia.
                                   lia.
                              lia.
                         lia.
                    lia.
               lia.
          lia.
     lia.
  lia.
Qed.