Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.

Definition is_prime_spec (n : nat) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 ->
   ((exists i, 2 <= i < n /\ n mod i = 0) -> result = false) /\
   ((forall i, 2 <= i < n -> n mod i <> 0) -> result = true)).

Example test_is_prime_11 : is_prime_spec 11 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros H_le.
    lia.
  - intros H_gt.
    split.
    + intros [i [H_bounds H_mod]].
      assert (H_cases: i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
      destruct H_cases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]; simpl in H_mod; discriminate.
    + intros H_forall.
      reflexivity.
Qed.