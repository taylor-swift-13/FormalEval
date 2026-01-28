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

Example problem_121_test_case :
  problem_121_spec [3%nat; 13%nat; 2%nat; 9%nat] 3%nat.
Proof.
  unfold problem_121_spec.
  eapply (soep_match 3%nat [13%nat; 2%nat; 9%nat] 0%nat 0%nat).
  - reflexivity.
  - reflexivity.
  - eapply (soep_skip 13%nat [2%nat; 9%nat] 1%nat 0%nat).
    + left; reflexivity.
    + eapply (soep_skip 2%nat [9%nat] 2%nat 0%nat).
      * right; reflexivity.
      * eapply (soep_skip 9%nat [] 3%nat 0%nat).
        { left; reflexivity. }
        { apply soep_nil. }
Qed.