Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_10000000031 : is_prime_spec 10000000031 false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true -> prime ... *)
    intros H.
    discriminate H.
  - (* Case: prime ... -> false = true *)
    intros Hprime.
    (* Definition of prime in Znumtheory: 1 < p /\ (forall n, 1 <= n < p -> rel_prime n p) *)
    destruct Hprime as [_ Hrel].
    (* We use 7 as a witness to disprove primality *)
    assert (Hrange: 1 <= 7 < 10000000031) by lia.
    specialize (Hrel 7 Hrange).
    (* rel_prime 7 ... is defined as Zis_gcd 7 ... 1 *)
    unfold rel_prime in Hrel.
    (* Zis_gcd is inductive; we extract the maximality property *)
    (* Zis_gcd_intro : ... -> (forall x, x|a -> x|b -> x|g) -> ... *)
    destruct Hrel as [_ _ Hgcd].
    (* Prove that 7 divides 7 and 7 divides 10000000031 *)
    assert (Hdiv7: (7 | 7)). { exists 1. lia. }
    assert (HdivBig: (7 | 10000000031)). { exists 1428571433. reflexivity. }
    (* Consequently, 7 must divide the GCD (which is 1) *)
    specialize (Hgcd 7 Hdiv7 HdivBig).
    (* Unfold divide to derive contradiction: 1 = x * 7 has no integer solution *)
    destruct Hgcd as [x Hx].
    lia.
Qed.