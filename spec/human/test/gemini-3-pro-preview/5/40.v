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

Example test_example : problem_5_spec [1%Z; 2%Z; 3%Z; 4%Z] [1%Z; 10000%Z; 2%Z; 10000%Z; 3%Z; 10000%Z; 4%Z] 10000%Z.
Proof.
  unfold problem_5_spec.
  split.
  - (* Case 1: input = [] -> output = [] *)
    intros H.
    discriminate H.
  - (* Case 2: Handling the non-empty logic *)
    intros n Hlen Hle.
    simpl in Hlen.
    subst n.
    split.
    + (* length output = 2 * 4 - 1 *)
      reflexivity.
    + (* forall i, i < 7 -> ... *)
      intros i Hi.
      (* We destruct i 7 times to handle indices 0 to 6 individually *)
      do 7 (destruct i as [|i]; [
        split; [
          intros He; try (destruct He; lia); try reflexivity |
          intros Ho; try (destruct Ho; lia); try reflexivity
        ] |
      ]).
      (* Case i >= 7 *)
      exfalso; lia.
Qed.