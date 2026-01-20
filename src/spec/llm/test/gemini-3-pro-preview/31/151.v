Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_42045 : is_prime_spec 42045 false.
Proof.
  unfold is_prime_spec.
  split.
  - intros H.
    discriminate H.
  - intros Hprime.
    destruct Hprime as [_ Hrel].
    assert (Hrange: 1 <= 5 < 42045) by lia.
    specialize (Hrel 5 Hrange).
    unfold rel_prime in Hrel.
    destruct Hrel as [_ _ Hgcd].
    assert (Hdiv5: (5 | 5)). { exists 1. lia. }
    assert (HdivN: (5 | 42045)). { exists 8409. lia. }
    specialize (Hgcd 5 Hdiv5 HdivN).
    destruct Hgcd as [x Hx].
    lia.
Qed.