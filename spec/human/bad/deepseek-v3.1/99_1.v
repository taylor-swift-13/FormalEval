Require Import ZArith Reals.
Open Scope Z_scope.
Open Scope R_scope.

Definition problem_99_pre (r : R) : Prop := True.

Definition problem_99_spec (r : R) (res : Z) : Prop :=
  (forall z : Z, Rabs (r - IZR res) <= Rabs (r - IZR z))
  /\
  (forall z : Z, Rabs (r - IZR res) = Rabs (r - IZR z) /\ res <> z -> Rabs (IZR res) >= Rabs (IZR z)).

Example test_closest_integer_10 : problem_99_spec 10 10.
Proof.
  unfold problem_99_spec.
  split.
  - (* First condition: 10 is the closest integer to 10 *)
    intro z.
    unfold IZR.
    simpl.
    rewrite Rminus_diag.
    rewrite Rabs_R0.
    apply Rabs_pos.
  - (* Second condition: no other integer at equal distance *)
    intro z.
    intro H.
    destruct H as [Hdist Hneq].
    unfold IZR in Hdist.
    simpl in Hdist.
    rewrite Rminus_diag in Hdist.
    rewrite Rabs_R0 in Hdist.
    (* Now we have |10 - IZR z| = 0, so 10 - IZR z = 0 *)
    symmetry in Hdist.
    apply Rabs_eq_0 in Hdist.
    (* This gives us 10 = IZR z *)
    apply Rminus_diag_eq in Hdist.
    apply eq_IZR in Hdist.
    (* Now we have 10%Z = z *)
    exfalso.
    apply Hneq.
    symmetry.
    assumption.
Qed.