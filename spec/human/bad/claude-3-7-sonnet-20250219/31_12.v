Require Import Arith.
Require Import Lia.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_is_prime_255379 :
  problem_31_spec 255379 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  + intros [Hgt Hdiv].
    assert (Hmod := Nat.mod_divides 255379 13).
    destruct Hmod as [k Hk].
    assert (Hdiv_13: 255379 mod 13 = 0).
    { rewrite Hk. simpl. apply Nat.mod_mul.
      lia. }
    specialize (Hdiv 13 Hdiv_13).
    destruct Hdiv as [H1 | Hn].
    - discriminate H1.
    - lia.
  + intros H.
    discriminate H.
Qed.