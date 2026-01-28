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

Example test_case : problem_5_spec [1; 2; 3; 4] [1; 9; 2; 9; 3; 9; 4] 9.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. discriminate H.
  - intros n Hlen Hn.
    replace n with 4%nat by (simpl in Hlen; lia).
    split.
    + reflexivity.
    + intros i Hi.
      do 7 (destruct i as [|i]; [
        split; intros H; try (destruct H as [k Hk]; lia); try reflexivity
      | ]).
      simpl in Hi. lia.
Qed.