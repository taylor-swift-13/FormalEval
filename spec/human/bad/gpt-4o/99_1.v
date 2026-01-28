Require Import ZArith Reals Psatz.
Open Scope Z_scope.
Open Scope R_scope.

Definition problem_99_pre (r : R) : Prop := True.

Definition problem_99_spec (r : R) (res : Z) : Prop :=
  (forall z : Z, Rabs (r - IZR res) <= Rabs (r - IZR z))
  /\
  (forall z : Z, Rabs (r - IZR res) = Rabs (r - IZR z) /\ res <> z -> Rabs (IZR res) >= Rabs (IZR z)).

Example test_closest_integer : problem_99_spec 10 10%Z.
Proof.
  unfold problem_99_spec.
  split.
  - intros z.
    destruct (Z.eq_dec z 10).
    + subst. 
      rewrite Rminus_diag_eq with (x := IZR 10); try reflexivity.
      rewrite Rabs_R0. apply Rle_refl.
    + assert (Habs : Rabs (10 - IZR z) >= 1).
      {
        unfold Rabs.
        destruct (Rcase_abs (10 - IZR z)).
        - apply Ropp_le_cancel. rewrite Ropp_involutive.
          apply Rplus_le_reg_r with (r := IZR z); ring_simplify.
          apply IZR_lt. lia.
        - apply Rplus_le_reg_r with (r := IZR z); ring_simplify.
          apply IZR_lt. lia.
      }
      rewrite Rminus_diag_eq with (x := IZR 10); try reflexivity.
      rewrite Rabs_R0. lra.
  - intros z [Habs Hneq].
    assert (H : z = 10).
    {
      unfold Rabs in Habs.
      destruct (Rcase_abs (10 - IZR res)); destruct (Rcase_abs (10 - IZR z)); 
      try lra.
    }
    subst. contradiction.
Qed.