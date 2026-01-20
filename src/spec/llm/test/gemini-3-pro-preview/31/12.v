Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_255379 : is_prime_spec 255379 false.
Proof.
  unfold is_prime_spec.
  split.
  - intros H.
    discriminate H.
  - intros Hprime.
    destruct Hprime as [_ Hrel].
    assert (Hrange: 1 <= 19 < 255379) by lia.
    specialize (Hrel 19 Hrange).
    unfold rel_prime in Hrel.
    destruct Hrel as [_ _ Hgcd].
    assert (Hdiv1: (19 | 19)). { exists 1. lia. }
    assert (Hdiv2: (19 | 255379)). { exists 13441. lia. }
    specialize (Hgcd 19 Hdiv1 Hdiv2).
    destruct Hgcd as [x Hx].
    lia.
Qed.