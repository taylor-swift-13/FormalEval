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

Example test_case : problem_121_spec [12; 22; 32; 44; 55; 66; 77; 88; 99] 231.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 12. Position is even (0), Value is even (12). Apply skip. *)
  apply soep_skip.
  - right. reflexivity.
  - (* Index 1: Value 22. Position is odd (1). Apply skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: Value 32. Position is even (2), Value is even (32). Apply skip. *)
      apply soep_skip.
      * right. reflexivity.
      * (* Index 3: Value 44. Position is odd (3). Apply skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: Value 55. Position is even (4), Value is odd (55). Apply match. *)
           (* We need 55 + 176 = 231, so s_tail must be 176. *)
           apply soep_match with (s_tail := 176).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: Value 66. Position is odd (5). Apply skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: Value 77. Position is even (6), Value is odd (77). Apply match. *)
                 (* We need 77 + 99 = 176, so s_tail must be 99. *)
                 apply soep_match with (s_tail := 99).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: Value 88. Position is odd (7). Apply skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: Value 99. Position is even (8), Value is odd (99). Apply match. *)
                         (* We need 99 + 0 = 99, so s_tail must be 0. *)
                         apply soep_match with (s_tail := 0).
                         *** reflexivity.
                         *** reflexivity.
                         *** (* Index 9: Empty list. Base case. *)
                             apply soep_nil.
Qed.