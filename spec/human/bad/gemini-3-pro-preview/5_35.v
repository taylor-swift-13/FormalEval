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

Example test_example : problem_5_spec [7%Z; 3%Z; 6%Z; 8%Z; 4%Z; 2%Z; 1%Z] [7%Z; -1%Z; 3%Z; -1%Z; 6%Z; -1%Z; 8%Z; -1%Z; 4%Z; -1%Z; 2%Z; -1%Z; 1%Z] (-1)%Z.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. discriminate H.
  - intros n Hlen Hle.
    simpl in Hlen. injection Hlen as Hn. subst n.
    split.
    + reflexivity.
    + intros i Hi.
      do 13 (destruct i as [|i]; [
        split; [
          intros He; try (vm_compute; reflexivity); try (exfalso; unfold Nat.Even in He; destruct He; lia)
        |
          intros Ho; try (vm_compute; reflexivity); try (exfalso; unfold Nat.Odd in Ho; destruct Ho; lia)
        ]
      | simpl in Hi ]).
      exfalso; lia.
Qed.