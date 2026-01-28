Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Definition Rfloor (x : R) : Z := up x - 1.

Lemma Rfloor_spec : forall x : R, IZR (Rfloor x) <= x < IZR (Rfloor x) + 1.
Proof.
  intros x.
  unfold Rfloor.
  destruct (archimed x) as [H1 H2].
  rewrite minus_IZR.
  simpl.
  lra.
Qed.

Definition problem_2_pre(x : R) : Prop :=
  x > 0.

Definition problem_2_spec (x frac : R) : Prop :=
  frac = x - IZR (Rfloor x) /\
  0 <= frac < 1.

Definition input_val : R := 10291122396192739 / 1000000000000000.
Definition output_val : R := 2911223961927387 / 10000000000000000.

Lemma floor_input : Rfloor input_val = 10%Z.
Proof.
  unfold Rfloor, input_val.
  assert (H: up (10291122396192739 / 1000000000000000) = 11%Z).
  {
    symmetry.
    apply tech_up; simpl; lra.
  }
  rewrite H.
  reflexivity.
Qed.

Example test_problem_2 : problem_2_spec input_val output_val.
Proof.
  unfold problem_2_spec, input_val, output_val.
  split.
  - assert (Hfloor: Rfloor (10291122396192739 / 1000000000000000) = 10%Z).
    {
      unfold Rfloor.
      assert (H: up (10291122396192739 / 1000000000000000) = 11%Z).
      {
        symmetry.
        apply tech_up; simpl; lra.
      }
      rewrite H.
      reflexivity.
    }
    rewrite Hfloor.
    simpl.
    lra.
  - lra.
Qed.