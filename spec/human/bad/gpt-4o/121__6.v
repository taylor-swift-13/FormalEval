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

Example test_case_1 : problem_121_spec [30; 13; 23; 32] 23.
Proof.
  unfold problem_121_spec.
  apply (soep_skip 30 [13; 23; 32] 0 23).
  - simpl. right. reflexivity.
  - apply (soep_match 13 [23; 32] 1 23).
    + simpl. reflexivity.
    + simpl. reflexivity.
    + apply (soep_match 23 [32] 2 0).
      * simpl. reflexivity.
      * simpl. reflexivity.
      * apply (soep_skip 32 [] 3 0).
        { simpl. right. reflexivity. }
        { apply soep_nil. }
Qed.