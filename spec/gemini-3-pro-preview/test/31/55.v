Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_1234563 : is_prime_spec 1234563 false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true -> prime 1234563 *)
    intros H.
    discriminate H.
  - (* Case: prime 1234563 -> false = true *)
    intros Hprime.
    (* Definition of prime in Znumtheory: 1 < p /\ (forall n, 1 <= n < p -> rel_prime n p) *)
    destruct Hprime as [_ Hrel].
    (* We use 3 as a witness to disprove primality, since 1+2+3+4+5+6+3 = 24 is divisible by 3 *)
    assert (Hrange: 1 <= 3 < 1234563) by lia.
    specialize (Hrel 3 Hrange).
    (* rel_prime 3 1234563 is defined as Zis_gcd 3 1234563 1 *)
    unfold rel_prime in Hrel.
    destruct Hrel as [_ _ Hgcd].
    (* Prove that 3 divides 3 and 3 divides 1234563 *)
    assert (Hdiv3: (3 | 3)). { exists 1. lia. }
    assert (HdivBig: (3 | 1234563)). { exists 411521. lia. }
    (* Consequently, 3 must divide the GCD (which is 1) *)
    specialize (Hgcd 3 Hdiv3 HdivBig).
    (* Unfold divide to derive contradiction *)
    destruct Hgcd as [x Hx].
    lia.
Qed.