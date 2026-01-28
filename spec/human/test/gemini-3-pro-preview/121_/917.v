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

Example test_case : problem_121_spec [30; 42; 5; 97; 120; 75; 75; 97] 80.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 30. Position is even (0), Value is even (30). Apply skip. *)
  apply soep_skip.
  - right. reflexivity.
  - (* Index 1: Value 42. Position is odd (1). Apply skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: Value 5. Position is even (2), Value is odd (5). Apply match. *)
      (* We need 5 + 75 = 80, so s_tail must be 75. *)
      apply soep_match with (s_tail := 75).
      * reflexivity.
      * reflexivity.
      * (* Index 3: Value 97. Position is odd (3). Apply skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: Value 120. Position is even (4), Value is even (120). Apply skip. *)
           apply soep_skip.
           ++ right. reflexivity.
           ++ (* Index 5: Value 75. Position is odd (5). Apply skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: Value 75. Position is even (6), Value is odd (75). Apply match. *)
                 (* We need 75 + 0 = 75, so s_tail must be 0. *)
                 apply soep_match with (s_tail := 0).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: Value 97. Position is odd (7). Apply skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: Empty list. Base case. *)
                         apply soep_nil.
Qed.