Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_9004 : is_prime_spec 9004 false.
Proof.
  unfold is_prime_spec.
  split.
  - intros H.
    discriminate H.
  - intros Hprime.
    destruct Hprime as [_ Hrel].
    assert (Hrange: 1 <= 2 < 9004) by lia.
    specialize (Hrel 2 Hrange).
    unfold rel_prime in Hrel.
    destruct Hrel as [_ _ Hgcd].
    assert (Hdiv2: (2 | 2)). { exists 1. lia. }
    assert (Hdiv9004: (2 | 9004)). { exists 4502. lia. }
    specialize (Hgcd 2 Hdiv2 Hdiv9004).
    destruct Hgcd as [x Hx].
    lia.
Qed.