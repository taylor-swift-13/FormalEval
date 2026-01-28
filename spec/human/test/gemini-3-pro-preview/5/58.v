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

Example test_example : problem_5_spec [7; 1; 1; 1; 1; 1; 1]%Z [7; -5; 1; -5; 1; -5; 1; -5; 1; -5; 1; -5; 1]%Z (-5)%Z.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. discriminate.
  - intros n Hlen Hle.
    simpl in Hlen. subst n.
    split.
    + simpl. reflexivity.
    + intros i Hi.
      do 13 (destruct i as [|i]; [
        split; [
          intros He; try (destruct He; lia); simpl; reflexivity
        |
          intros Ho; try (destruct Ho; lia); simpl; reflexivity
        ]
      | ]).
      exfalso; lia.
Qed.