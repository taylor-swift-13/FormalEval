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

Example test_is_prime_1011 : is_prime_spec 1011 false.
Proof.
  unfold is_prime_spec.
  split.
  - intros H_le.
    lia.
  - intros H_gt.
    split.
    + intros H_exists.
      reflexivity.
    + intros H_forall.
      assert (H_bounds : 2 <= 3 < 1011). { lia. }
      specialize (H_forall 3 H_bounds).
      assert (H_mod : 1011 mod 3 = 0). { reflexivity. }
      rewrite H_mod in H_forall.
      contradiction.
Qed.