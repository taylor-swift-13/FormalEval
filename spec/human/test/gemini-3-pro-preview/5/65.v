Require Import List.
Require Import ZArith.
Require Import Arith.
Require Import Nat.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition problem_5_pre (input output : list Z) : Prop := True.

Definition problem_5_spec (input output : list Z) (d : Z) : Prop :=
  (input = [] -> output = []) /\
  (forall n : nat,
      length input = n -> 1 <= n ->
      length output = 2 * n - 1 /\
      forall i : nat, i < 2 * n - 1 ->
        (Nat.Even i -> nth_error output i = nth_error input (i / 2)) /\
        (Nat.Odd i -> nth_error output i = Some d)
  ).

Example test_example : problem_5_spec [2%Z; 3%Z; 4%Z] [2%Z; 10001%Z; 3%Z; 10001%Z; 4%Z] 10001%Z.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. discriminate H.
  - intros n Hlen Hle.
    simpl in Hlen. subst n.
    split.
    + reflexivity.
    + intros i Hi.
      do 5 (destruct i as [|i]; [
        simpl; split; [
          intros He; try reflexivity; try (exfalso; destruct He; lia) |
          intros Ho; try reflexivity; try (exfalso; destruct Ho; lia)
        ]
      | ]).
      lia.
Qed.