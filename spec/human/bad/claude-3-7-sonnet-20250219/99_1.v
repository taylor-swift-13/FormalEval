Require Import ZArith Reals.
Open Scope Z_scope.
Open Scope R_scope.

Definition problem_99_pre (r : R) : Prop := True.

Definition problem_99_spec (r : R) (res : Z) : Prop :=
  (forall z : Z, Rabs (r - IZR res) <= Rabs (r - IZR z))
  /\
  (forall z : Z, Rabs (r - IZR res) = Rabs (r - IZR z) /\ res <> z -> Rabs (IZR res) >= Rabs (IZR z)).

Example closest_integer_10_example :
  problem_99_spec 10 10%Z.
Proof.
  unfold problem_99_spec.
  split.

  - intros z.
    (* Distance from 10 to 10 *)
    replace (Rabs (10 - IZR 10)) with 0.
    + apply Rle_0_abs.
    + simpl. rewrite Rminus_diag_eq; [reflexivity| apply Rle_refl].

  - intros z [Hdist_eq Hz_neq].
    (* Replace Rabs (10 - IZR 10) by 0 in Hdist_eq *)
    replace (Rabs (10 - IZR 10)) with 0 in Hdist_eq.
    + (* So Rabs (10 - IZR z) = 0 *)
      apply Rabs_eq_0 in Hdist_eq.
      subst.
      apply IZR_inj in Hz_neq.
      contradiction.
    + simpl. rewrite Rminus_diag_eq; [reflexivity| apply Rle_refl].
Qed.