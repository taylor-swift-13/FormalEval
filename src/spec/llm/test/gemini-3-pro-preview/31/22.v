Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_1234567 : is_prime_spec 1234567 false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true -> prime 1234567 *)
    intros H.
    discriminate H.
  - (* Case: prime 1234567 -> false = true *)
    intros Hprime.
    (* Definition of prime in Znumtheory: 1 < p /\ (forall n, 1 <= n < p -> rel_prime n p) *)
    destruct Hprime as [_ Hrel].
    (* We use 127 as a witness to disprove primality *)
    assert (Hrange: 1 <= 127 < 1234567) by lia.
    specialize (Hrel 127 Hrange).
    (* rel_prime 127 1234567 is defined as Zis_gcd 127 1234567 1 *)
    unfold rel_prime in Hrel.
    (* Zis_gcd is inductive; we extract the maximality property *)
    (* Zis_gcd_intro : ... -> (forall x, x|a -> x|b -> x|g) -> ... *)
    destruct Hrel as [_ _ Hgcd].
    (* Prove that 127 divides 127 and 127 divides 1234567 *)
    assert (Hdiv1: (127 | 127)). { exists 1. lia. }
    assert (Hdiv2: (127 | 1234567)). { exists 9721. lia. }
    (* Consequently, 127 must divide the GCD (which is 1) *)
    specialize (Hgcd 127 Hdiv1 Hdiv2).
    (* Unfold divide to derive contradiction: 1 = x * 127 has no integer solution *)
    destruct Hgcd as [x Hx].
    lia.
Qed.