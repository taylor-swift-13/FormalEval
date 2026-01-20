Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_10000000027 : is_prime_spec 10000000027 false.
Proof.
  unfold is_prime_spec.
  split.
  - intros H.
    discriminate H.
  - intros Hprime.
    destruct Hprime as [_ Hrel].
    assert (Hrange: 1 <= 37 < 10000000027) by lia.
    specialize (Hrel 37 Hrange).
    unfold rel_prime in Hrel.
    destruct Hrel as [_ _ Hgcd].
    assert (Hdiv37: (37 | 37)). { exists 1. lia. }
    assert (HdivBig: (37 | 10000000027)). { exists 270270271. lia. }
    specialize (Hgcd 37 Hdiv37 HdivBig).
    destruct Hgcd as [x Hx].
    lia.
Qed.