Require Import Arith.
Require Import Lia.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_is_prime_85 :
  problem_31_spec 85 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  + intros [Hgt Hdiv].
    assert (85 mod 5 = 0) by reflexivity.
    specialize (Hdiv 5 H).
    destruct Hdiv as [H5 | H5].
    - discriminate H5.
    - discriminate H5.
  + intros H.
    discriminate H.
Qed.