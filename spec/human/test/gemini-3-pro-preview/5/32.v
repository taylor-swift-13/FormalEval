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

Example test_case : problem_5_spec [1; 1; 1; 1; 1; 1] [1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1] 0.
Proof.
  unfold problem_5_spec.
  split.
  - intro H.
    discriminate H.
  - intros n Hlen Hn.
    simpl in Hlen.
    subst n.
    split.
    + reflexivity.
    + intros i Hi.
      do 11 (destruct i as [|i]; [
        split; [
          intro He; try reflexivity; try (destruct He; exfalso; lia) |
          intro Ho; try reflexivity; try (destruct Ho; exfalso; lia)
        ]
      | ]).
      exfalso; lia.
Qed.