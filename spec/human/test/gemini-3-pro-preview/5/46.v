Require Import List.
Require Import ZArith.
Require Import Arith.
Require Import Nat.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.
Open Scope Z_scope.
Import ListNotations.

Definition problem_5_pre (input output : list Z) : Prop := True.

Definition problem_5_spec (input output : list Z) (d : Z) : Prop :=
  (input = [] -> output = []) /\
  (forall n : nat,
      length input = n -> (1 <= n)%nat ->
      length output = (2 * n - 1)%nat /\
      forall i : nat, (i < 2 * n - 1)%nat ->
        (Nat.Even i -> nth_error output i = nth_error input (i / 2)) /\
        (Nat.Odd i -> nth_error output i = Some d)
  ).

Example test_case : problem_5_spec [3; 6; 2; 3; 5; 1] [3; -1; 6; -1; 2; -1; 3; -1; 5; -1; 1] (-1).
Proof.
  unfold problem_5_spec.
  split.
  - intros H. discriminate.
  - intros n Hlen Hn.
    simpl in Hlen. inversion Hlen. subst n.
    split.
    + reflexivity.
    + intros i Hi.
      split; intros Hparity.
      * do 11 (destruct i; [ simpl; try reflexivity; try (destruct Hparity as [? ?]; lia) | ]).
        exfalso; lia.
      * do 11 (destruct i; [ simpl; try reflexivity; try (destruct Hparity as [? ?]; lia) | ]).
        exfalso; lia.
Qed.