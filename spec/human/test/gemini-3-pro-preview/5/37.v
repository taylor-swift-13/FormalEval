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

Example test_example : problem_5_spec [1%Z; 2%Z; 3%Z; 4%Z] [1%Z; 4%Z; 2%Z; 4%Z; 3%Z; 4%Z; 4%Z] 4%Z.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. discriminate H.
  - intros n Hlen Hle.
    simpl in Hlen. subst n.
    split.
    + reflexivity.
    + intros i Hi.
      repeat (destruct i as [|i]; [ clear Hi | try lia ]).
      all: split; intros H.
      all: try (inversion H as [k Hk]; lia).
      all: try reflexivity.
Qed.