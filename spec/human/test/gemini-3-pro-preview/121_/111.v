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

Example test_case : problem_121_spec [11; 22; 33; 44; 55; 66; 77; 88; 99] 275.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 11. Position even (0), Value odd (11). Apply match. *)
  (* We need 11 + 264 = 275, so s_tail must be 264. *)
  apply soep_match with (s_tail := 264).
  - (* Verify index is even *)
    reflexivity.
  - (* Verify value is odd *)
    reflexivity.
  - (* Recurse to tail *)
    (* Index 1: Value 22. Position odd (1). Apply skip. *)
    apply soep_skip.
    + (* Verify condition: index is odd *)
      left. reflexivity.
    + (* Recurse to tail *)
      (* Index 2: Value 33. Position even (2), Value odd (33). Apply match. *)
      (* We need 33 + 231 = 264, so s_tail must be 231. *)
      apply soep_match with (s_tail := 231).
      * (* Verify index is even *)
        reflexivity.
      * (* Verify value is odd *)
        reflexivity.
      * (* Recurse to tail *)
        (* Index 3: Value 44. Position odd (3). Apply skip. *)
        apply soep_skip.
        -- (* Verify condition: index is odd *)
           left. reflexivity.
        -- (* Recurse to tail *)
           (* Index 4: Value 55. Position even (4), Value odd (55). Apply match. *)
           (* We need 55 + 176 = 231, so s_tail must be 176. *)
           apply soep_match with (s_tail := 176).
           ++ (* Verify index is even *)
              reflexivity.
           ++ (* Verify value is odd *)
              reflexivity.
           ++ (* Recurse to tail *)
              (* Index 5: Value 66. Position odd (5). Apply skip. *)
              apply soep_skip.
              ** (* Verify condition: index is odd *)
                 left. reflexivity.
              ** (* Recurse to tail *)
                 (* Index 6: Value 77. Position even (6), Value odd (77). Apply match. *)
                 (* We need 77 + 99 = 176, so s_tail must be 99. *)
                 apply soep_match with (s_tail := 99).
                 --- (* Verify index is even *)
                     reflexivity.
                 --- (* Verify value is odd *)
                     reflexivity.
                 --- (* Recurse to tail *)
                     (* Index 7: Value 88. Position odd (7). Apply skip. *)
                     apply soep_skip.
                     +++ (* Verify condition: index is odd *)
                         left. reflexivity.
                     +++ (* Recurse to tail *)
                         (* Index 8: Value 99. Position even (8), Value odd (99). Apply match. *)
                         (* We need 99 + 0 = 99, so s_tail must be 0. *)
                         apply soep_match with (s_tail := 0).
                         *** (* Verify index is even *)
                             reflexivity.
                         *** (* Verify value is odd *)
                             reflexivity.
                         *** (* Recurse to tail *)
                             (* Index 9: Empty list. Base case. *)
                             apply soep_nil.
Qed.