Require Import Arith.
Require Import Lia.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_is_prime_255379 : problem_31_spec 255379 false.
Proof.
  unfold problem_31_spec.
  unfold IsPrime.
  split.
  - intros [H1 H2].
    specialize (H2 293).
    assert (255379 mod 293 = 0) as Hmod by native_compute.
    specialize (H2 Hmod).
    destruct H2 as [H2 | H2].
    + discriminate.
    + assert (293 <> 255379) as Hneq by lia.
      contradiction.
  - intros H. discriminate.
Qed.