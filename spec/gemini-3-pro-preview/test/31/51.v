Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_57 : is_prime_spec 57 false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true -> prime 57 *)
    intros H.
    discriminate H.
  - (* Case: prime 57 -> false = true *)
    intros Hprime.
    (* Definition of prime in Znumtheory: 1 < p /\ (forall n, 1 <= n < p -> rel_prime n p) *)
    destruct Hprime as [_ Hrel].
    (* We use 3 as a witness to disprove primality *)
    assert (Hrange: 1 <= 3 < 57) by lia.
    specialize (Hrel 3 Hrange).
    (* rel_prime 3 57 is defined as Zis_gcd 3 57 1 *)
    unfold rel_prime in Hrel.
    (* Zis_gcd is inductive; we extract the maximality property *)
    (* Zis_gcd_intro : ... -> (forall x, x|a -> x|b -> x|g) -> ... *)
    destruct Hrel as [_ _ Hgcd].
    (* Prove that 3 divides 3 and 3 divides 57 *)
    assert (Hdiv3: (3 | 3)). { exists 1. lia. }
    assert (Hdiv57: (3 | 57)). { exists 19. lia. }
    (* Consequently, 3 must divide the GCD (which is 1) *)
    specialize (Hgcd 3 Hdiv3 Hdiv57).
    (* Unfold divide to derive contradiction: 1 = x * 3 has no integer solution *)
    destruct Hgcd as [x Hx].
    lia.
Qed.