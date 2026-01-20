Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_123456789 : is_prime_spec 123456789 false.
Proof.
  unfold is_prime_spec.
  split.
  - intros H.
    discriminate H.
  - intros Hprime.
    destruct Hprime as [_ Hrel].
    assert (Hrange: 1 <= 3 < 123456789) by lia.
    specialize (Hrel 3 Hrange).
    unfold rel_prime in Hrel.
    destruct Hrel as [_ _ Hgcd].
    assert (Hdiv3: (3 | 3)). { exists 1. lia. }
    assert (HdivBig: (3 | 123456789)). { exists 41152263. lia. }
    specialize (Hgcd 3 Hdiv3 HdivBig).
    destruct Hgcd as [x Hx].
    lia.
Qed.