Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_10 : is_prime_spec 10 false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true -> prime 10 *)
    intros H.
    discriminate H.
  - (* Case: prime 10 -> false = true *)
    intros Hprime.
    (* Definition of prime in Znumtheory: 1 < p /\ (forall n, 1 <= n < p -> rel_prime n p) *)
    destruct Hprime as [_ Hrel].
    (* We use 2 as a witness to disprove primality *)
    assert (Hrange: 1 <= 2 < 10) by lia.
    specialize (Hrel 2 Hrange).
    (* rel_prime 2 10 is defined as Zis_gcd 2 10 1 *)
    unfold rel_prime in Hrel.
    (* Zis_gcd is inductive; we extract the maximality property *)
    (* Zis_gcd_intro : ... -> (forall x, x|a -> x|b -> x|g) -> ... *)
    destruct Hrel as [_ _ Hgcd].
    (* Prove that 2 divides 2 and 2 divides 10 *)
    assert (Hdiv2: (2 | 2)). { exists 1. lia. }
    assert (Hdiv10: (2 | 10)). { exists 5. lia. }
    (* Consequently, 2 must divide the GCD (which is 1) *)
    specialize (Hgcd 2 Hdiv2 Hdiv10).
    (* Unfold divide to derive contradiction: 1 = x * 2 has no integer solution *)
    destruct Hgcd as [x Hx].
    lia.
Qed.