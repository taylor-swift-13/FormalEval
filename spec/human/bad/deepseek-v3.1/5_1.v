Require Import List.
Require Import ZArith.
Require Import Arith.
Require Import Nat.
Require Import Lia.
Require Import PeanoNat.
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

Example test_empty : problem_5_spec [] [] 7.
Proof.
  unfold problem_5_spec.
  split.
  - intro H. reflexivity.
  - intros n Hlen Hn.
    exfalso.
    rewrite Hlen in Hn.
    simpl in Hn.
    lia.
Qed.