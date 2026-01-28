Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.

Inductive sum_odd_in_even_pos_rel : list nat -> nat -> nat -> Prop :=
| soep_nil : forall i, sum_odd_in_even_pos_rel nil i 0%nat
| soep_match : forall h t i s_tail, Nat.even i = true -> Nat.even h = false ->
    sum_odd_in_even_pos_rel t (S i) s_tail ->
    sum_odd_in_even_pos_rel (h :: t) i (h + s_tail)
| soep_skip : forall h t i s_tail, (Nat.even i = false \/ Nat.even h = true) ->
    sum_odd_in_even_pos_rel t (S i) s_tail ->
    sum_odd_in_even_pos_rel (h :: t) i s_tail.

(* 非空整数列表 *)
Definition problem_121_pre (l : list nat) : Prop := l <> [].

Definition problem_121_spec (l : list nat) (output : nat) : Prop :=
  sum_odd_in_even_pos_rel l 0%nat output.

Example test_case : problem_121_spec [2; 11; 3; 4; 5; 88; 5; 76; 55; 11; 8; 8; 8] 68.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 2. Position is even (0), Value is even (2). Apply skip. *)
  apply soep_skip.
  - right. reflexivity.
  - (* Index 1: Value 11. Position is odd (1). Apply skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: Value 3. Position is even (2), Value is odd (3). Apply match. *)
      (* We need 3 + 65 = 68. *)
      apply soep_match with (s_tail := 65).
      * reflexivity.
      * reflexivity.
      * (* Index 3: Value 4. Position is odd (3). Apply skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: Value 5. Position is even (4), Value is odd (5). Apply match. *)
           (* We need 5 + 60 = 65. *)
           apply soep_match with (s_tail := 60).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: Value 88. Position is odd (5). Apply skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: Value 5. Position is even (6), Value is odd (5). Apply match. *)
                 (* We need 5 + 55 = 60. *)
                 apply soep_match with (s_tail := 55).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: Value 76. Position is odd (7). Apply skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: Value 55. Position is even (8), Value is odd (55). Apply match. *)
                         (* We need 55 + 0 = 55. *)
                         apply soep_match with (s_tail := 0).
                         *** reflexivity.
                         *** reflexivity.
                         *** (* Index 9: Value 11. Position is odd (9). Apply skip. *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* Index 10: Value 8. Position is even (10), Value is even (8). Apply skip. *)
                                  apply soep_skip.
                                  ++++ right. reflexivity.
                                  ++++ (* Index 11: Value 8. Position is odd (11). Apply skip. *)
                                       apply soep_skip.
                                       **** left. reflexivity.
                                       **** (* Index 12: Value 8. Position is even (12), Value is even (8). Apply skip. *)
                                            apply soep_skip.
                                            ----- right. reflexivity.
                                            ----- (* End of list *)
                                                  apply soep_nil.
Qed.