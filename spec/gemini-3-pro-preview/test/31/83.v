Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_7939 : is_prime_spec 7939 false.
Proof.
  unfold is_prime_spec.
  split.
  - intros H.
    discriminate H.
  - intros Hprime.
    destruct Hprime as [_ Hrel].
    assert (Hrange: 1 <= 17 < 7939) by lia.
    specialize (Hrel 17 Hrange).
    unfold rel_prime in Hrel.
    destruct Hrel as [_ _ Hgcd].
    assert (Hdiv17: (17 | 17)). { exists 1. lia. }
    assert (Hdiv7939: (17 | 7939)). { exists 467. lia. }
    specialize (Hgcd 17 Hdiv17 Hdiv7939).
    destruct Hgcd as [x Hx].
    lia.
Qed.