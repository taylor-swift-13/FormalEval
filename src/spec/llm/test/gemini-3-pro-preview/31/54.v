Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_3 : is_prime_spec 3 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros _.
    apply prime_intro.
    + lia.
    + intros n Hn.
      assert (H : n = 1 \/ n = 2) by lia.
      destruct H as [H1 | H2].
      * subst. apply rel_prime_1.
      * subst. apply rel_prime_sym.
        apply Zis_gcd_intro.
        -- exists 3. lia.
        -- exists 2. lia.
        -- intros x Hx3 Hx2.
           destruct Hx3 as [k3 Hk3].
           destruct Hx2 as [k2 Hk2].
           exists (k3 - k2).
           lia.
  - intros _. reflexivity.
Qed.