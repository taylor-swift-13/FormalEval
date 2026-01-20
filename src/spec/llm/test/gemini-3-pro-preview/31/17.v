Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_40 : is_prime_spec 40 false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true -> prime 40 *)
    intros H.
    discriminate H.
  - (* Case: prime 40 -> false = true *)
    intros Hprime.
    (* Definition of prime in Znumtheory: 1 < p /\ (forall n, 1 <= n < p -> rel_prime n p) *)
    destruct Hprime as [_ Hrel].
    (* We use 2 as a witness to disprove primality *)
    assert (Hrange: 1 <= 2 < 40) by lia.
    specialize (Hrel 2 Hrange).
    (* rel_prime 2 40 is defined as Zis_gcd 2 40 1 *)
    unfold rel_prime in Hrel.
    (* Zis_gcd is inductive; we extract the maximality property *)
    (* Zis_gcd_intro : ... -> (forall x, x|a -> x|b -> x|g) -> ... *)
    destruct Hrel as [_ _ Hgcd].
    (* Prove that 2 divides 2 and 2 divides 40 *)
    assert (Hdiv2: (2 | 2)). { exists 1. lia. }
    assert (Hdiv40: (2 | 40)). { exists 20. lia. }
    (* Consequently, 2 must divide the GCD (which is 1) *)
    specialize (Hgcd 2 Hdiv2 Hdiv40).
    (* Unfold divide to derive contradiction: 1 = x * 2 has no integer solution *)
    destruct Hgcd as [x Hx].
    lia.
Qed.