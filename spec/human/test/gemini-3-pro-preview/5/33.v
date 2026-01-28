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

Example test_case : problem_5_spec [-2; 5; 10; -5; 2] [-2; -8; 5; -8; 10; -8; -5; -8; 2] (-8).
Proof.
  unfold problem_5_spec.
  split.
  - intros H. discriminate.
  - intros n Hlen Hn.
    simpl in Hlen. rewrite <- Hlen.
    split.
    + simpl. reflexivity.
    + intros i Hi.
      do 9 (destruct i as [|i]; [
        split; [
          intros He;
          try (exfalso; unfold Nat.Even in He; destruct He as [x Hx]; lia);
          simpl; reflexivity
        | intros Ho;
          try (exfalso; unfold Nat.Odd in Ho; destruct Ho as [x Hx]; lia);
          simpl; reflexivity
        ]
      | ]).
      exfalso; lia.
Qed.