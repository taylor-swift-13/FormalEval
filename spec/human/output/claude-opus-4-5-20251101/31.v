Require Import Arith.
Require Import Lia.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_is_prime_6 : problem_31_spec 6 false.
Proof.
  unfold problem_31_spec.
  unfold IsPrime.
  split.
  - intros [H1 H2].
    (* 6 is not prime because 2 divides 6 and 2 is neither 1 nor 6 *)
    specialize (H2 2).
    assert (6 mod 2 = 0) as Hmod by reflexivity.
    specialize (H2 Hmod).
    destruct H2 as [H2 | H2]; discriminate.
  - intros H. discriminate.
Qed.