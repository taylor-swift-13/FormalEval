Require Import ZArith Reals.
Require Import Lra.
Open Scope Z_scope.
Open Scope R_scope.

Definition problem_99_pre (r : R) : Prop := True.

Definition problem_99_spec (r : R) (res : Z) : Prop :=
  (forall z : Z, Rabs (r - IZR res) <= Rabs (r - IZR z))
  /\
  (forall z : Z, Rabs (r - IZR res) = Rabs (r - IZR z) /\ res <> z -> Rabs (IZR res) >= Rabs (IZR z)).

Lemma Rabs_zero_iff : forall x : R, Rabs x = 0 -> x = 0.
Proof.
  intros x H.
  unfold Rabs in H.
  destruct (Rcase_abs x).
  - lra.
  - lra.
Qed.

Example test_closest_integer_10 : problem_99_spec 10 10%Z.
Proof.
  unfold problem_99_spec.
  split.
  - intros z.
    replace (10 - IZR 10) with 0 by (simpl; lra).
    rewrite Rabs_R0.
    apply Rabs_pos.
  - intros z [H1 H2].
    replace (10 - IZR 10) with 0 in H1 by (simpl; lra).
    rewrite Rabs_R0 in H1.
    symmetry in H1.
    apply Rabs_zero_iff in H1.
    assert (Heq: IZR z = 10) by lra.
    apply eq_IZR in Heq.
    contradiction.
Qed.