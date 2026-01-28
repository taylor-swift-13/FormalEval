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

Definition problem_121_pre (l : list nat) : Prop := l <> [].

Definition problem_121_spec (l : list nat) (output : nat) : Prop :=
  sum_odd_in_even_pos_rel l 0%nat output.

Example test_problem_121 : problem_121_spec [1; 2; 3; 13; 5; 6] 9.
Proof.
  unfold problem_121_spec.
  replace 9 with (1 + 8) by reflexivity.
  apply soep_match.
  - reflexivity.
  - reflexivity.
  - apply soep_skip.
    + right. reflexivity.
    + replace 8 with (3 + 5) by reflexivity.
      apply soep_match.
      * reflexivity.
      * reflexivity.
      * apply soep_skip.
        -- left. reflexivity.
        -- replace 5 with (5 + 0) by reflexivity.
           apply soep_match.
           ++ reflexivity.
           ++ reflexivity.
           ++ apply soep_skip.
              ** left. reflexivity.
              ** apply soep_nil.
Qed.