Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_26 : is_prime_spec 26 false.
Proof.
  unfold is_prime_spec.
  split.
  - intros H.
    discriminate H.
  - intros Hprime.
    destruct Hprime as [_ Hrel].
    assert (Hrange: 1 <= 2 < 26) by lia.
    specialize (Hrel 2 Hrange).
    unfold rel_prime in Hrel.
    destruct Hrel as [_ _ Hgcd].
    assert (Hdiv2: (2 | 2)). { exists 1. lia. }
    assert (Hdiv26: (2 | 26)). { exists 13. lia. }
    specialize (Hgcd 2 Hdiv2 Hdiv26).
    destruct Hgcd as [x Hx].
    lia.
Qed.