Require Import ZArith Reals Psatz Rbasic_fun.
Open Scope Z_scope.
Open Scope R_scope.

Definition problem_99_pre (r : R) : Prop := True.

Definition problem_99_spec (r : R) (res : Z) : Prop :=
  (forall z : Z, Rabs (r - IZR res) <= Rabs (r - IZR z))
  /\
  (forall z : Z, Rabs (r - IZR res) = Rabs (r - IZR z) /\ res <> z -> Rabs (IZR res) >= Rabs (IZR z)).

Example problem_99_test_10 : problem_99_spec 10%R 10%Z.
Proof.
  split.
  - intros z.
    assert (10 - IZR 10 = 0) as H0 by lra.
    rewrite H0.
    rewrite Rabs_R0.
    apply Rabs_pos.
  - intros z [Heq Hneq].
    assert (10 - IZR 10 = 0) as H0 by lra.
    rewrite H0 in Heq.
    rewrite Rabs_R0 in Heq.
    symmetry in Heq.
    apply Rabs_eq_0 in Heq.
    assert (IZR z = 10) as HzR by lra.
    assert (IZR 10 = 10) as H10R by lra.
    rewrite <- H10R in HzR.
    apply IZR_inj in HzR.
    subst z.
    unfold Rge.
    apply Rle_refl.
Qed.