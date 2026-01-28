Require Import Arith.
Require Import Lia.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_is_prime_33 :
  problem_31_spec 33 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  + intros [Hgt Hdiv].
    assert (33 mod 3 = 0) by reflexivity.
    specialize (Hdiv 3 H).
    destruct Hdiv as [H3 | H3].
    - discriminate H3.
    - discriminate H3.
  + intros H.
    discriminate H.
Qed.