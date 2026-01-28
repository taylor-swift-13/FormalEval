Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Example test_is_prime_5 : is_prime_spec 5 true.
Proof.
  unfold is_prime_spec.
  split.
  - intros _.
    apply prime_intro.
    + lia.
    + intros n Hn.
      unfold rel_prime.
      assert (H: Z.gcd n 5 = 1).
      {
        assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4) by lia.
        destruct H as [-> | [-> | [-> | ->]]]; compute; reflexivity.
      }
      rewrite <- H.
      apply Zgcd_is_gcd.
  - intros _. reflexivity.
Qed.