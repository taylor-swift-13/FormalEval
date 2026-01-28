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

Example test_case : problem_5_spec [1; 2; 3; 2] [1; 0; 2; 0; 3; 0; 2] 0.
Proof.
  unfold problem_5_spec.
  split.
  - (* Case: input = [] -> output = [] *)
    intros H.
    discriminate.
  - (* Case: Non-empty input constraints *)
    intros n Hlen Hn.
    simpl in Hlen.
    assert (n = 4%nat) by lia.
    subst n.
    split.
    + reflexivity.
    + intros i Hi.
      (* Check for i = 0 to 6 *)
      do 7 (destruct i as [|i]; [
        split; [
          intros He; try (exfalso; unfold Nat.Even in He; destruct He; lia); simpl; reflexivity
        | intros Ho; try (exfalso; unfold Nat.Odd in Ho; destruct Ho; lia); simpl; reflexivity
        ]
      | ]).
      (* Case i >= 7 *)
      exfalso; lia.
Qed.