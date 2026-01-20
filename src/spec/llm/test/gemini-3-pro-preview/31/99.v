Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_42041 : is_prime_spec 42041 false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true -> prime 42041 *)
    intros H.
    discriminate H.
  - (* Case: prime 42041 -> false = true *)
    intros Hprime.
    (* Definition of prime in Znumtheory: 1 < p /\ (forall n, 1 <= n < p -> rel_prime n p) *)
    destruct Hprime as [_ Hrel].
    (* We use 17 as a witness to disprove primality *)
    assert (Hrange: 1 <= 17 < 42041) by lia.
    specialize (Hrel 17 Hrange).
    (* rel_prime 17 42041 is defined as Zis_gcd 17 42041 1 *)
    unfold rel_prime in Hrel.
    (* Zis_gcd is inductive; we extract the maximality property *)
    (* Zis_gcd_intro : ... -> (forall x, x|a -> x|b -> x|g) -> ... *)
    destruct Hrel as [_ _ Hgcd].
    (* Prove that 17 divides 17 and 17 divides 42041 *)
    assert (Hdiv17: (17 | 17)). { exists 1. lia. }
    assert (Hdiv42041: (17 | 42041)). { exists 2473. lia. }
    (* Consequently, 17 must divide the GCD (which is 1) *)
    specialize (Hgcd 17 Hdiv17 Hdiv42041).
    (* Unfold divide to derive contradiction: 1 = x * 17 has no integer solution *)
    destruct Hgcd as [x Hx].
    lia.
Qed.