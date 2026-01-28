Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_7935 : is_prime_spec 7935 false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true -> prime 7935 *)
    intros H.
    discriminate H.
  - (* Case: prime 7935 -> false = true *)
    intros Hprime.
    (* Definition of prime in Znumtheory: 1 < p /\ (forall n, 1 <= n < p -> rel_prime n p) *)
    destruct Hprime as [_ Hrel].
    (* We use 5 as a witness to disprove primality *)
    assert (Hrange: 1 <= 5 < 7935) by lia.
    specialize (Hrel 5 Hrange).
    (* rel_prime 5 7935 is defined as Zis_gcd 5 7935 1 *)
    unfold rel_prime in Hrel.
    (* Zis_gcd is inductive; we extract the maximality property *)
    (* Zis_gcd_intro : ... -> (forall x, x|a -> x|b -> x|g) -> ... *)
    destruct Hrel as [_ _ Hgcd].
    (* Prove that 5 divides 5 and 5 divides 7935 *)
    assert (Hdiv5: (5 | 5)). { exists 1. lia. }
    assert (Hdiv7935: (5 | 7935)). { exists 1587. lia. }
    (* Consequently, 5 must divide the GCD (which is 1) *)
    specialize (Hgcd 5 Hdiv5 Hdiv7935).
    (* Unfold divide to derive contradiction: 1 = x * 5 has no integer solution *)
    destruct Hgcd as [x Hx].
    lia.
Qed.