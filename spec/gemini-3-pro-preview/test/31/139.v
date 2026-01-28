Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_93 : is_prime_spec 93 false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Case: false = true -> prime 93 *)
    intros H.
    discriminate H.
  - (* Case: prime 93 -> false = true *)
    intros Hprime.
    destruct Hprime as [_ Hrel].
    (* We use 3 as a witness to disprove primality since 93 = 3 * 31 *)
    assert (Hrange: 1 <= 3 < 93) by lia.
    specialize (Hrel 3 Hrange).
    unfold rel_prime in Hrel.
    destruct Hrel as [_ _ Hgcd].
    assert (Hdiv3: (3 | 3)). { exists 1. lia. }
    assert (Hdiv93: (3 | 93)). { exists 31. lia. }
    specialize (Hgcd 3 Hdiv3 Hdiv93).
    destruct Hgcd as [x Hx].
    lia.
Qed.