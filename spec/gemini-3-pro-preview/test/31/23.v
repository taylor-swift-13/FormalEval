Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_9000 : is_prime_spec 9000 false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true -> prime 9000 *)
    intros H.
    discriminate H.
  - (* Case: prime 9000 -> false = true *)
    intros Hprime.
    destruct Hprime as [_ Hrel].
    (* We use 2 as a witness to disprove primality *)
    assert (Hrange: 1 <= 2 < 9000) by lia.
    specialize (Hrel 2 Hrange).
    unfold rel_prime in Hrel.
    destruct Hrel as [_ _ Hgcd].
    (* Prove that 2 divides 2 and 2 divides 9000 *)
    assert (Hdiv2: (2 | 2)). { exists 1. lia. }
    assert (Hdiv9000: (2 | 9000)). { exists 4500. lia. }
    (* Consequently, 2 must divide the GCD (which is 1) *)
    specialize (Hgcd 2 Hdiv2 Hdiv9000).
    destruct Hgcd as [x Hx].
    lia.
Qed.