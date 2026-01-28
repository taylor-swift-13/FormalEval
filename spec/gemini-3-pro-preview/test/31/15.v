Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_2 : is_prime_spec 2 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros _.
    apply prime_intro.
    + lia.
    + intros n Hrange.
      assert (n = 1) by lia.
      subst n.
      apply Zis_gcd_intro.
      * exists 1. lia.
      * exists 2. lia.
      * intros x Hdiv1 Hdiv2. exact Hdiv1.
  - intros _. reflexivity.
Qed.