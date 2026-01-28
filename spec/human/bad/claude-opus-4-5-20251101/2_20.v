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

Definition input_val : R := 1.1369261836552624.
Definition output_val : R := 0.13692618365526243.

Lemma floor_input : Rfloor input_val = 1%Z.
Proof.
  unfold Rfloor, input_val.
  assert (H: up 1.1369261836552624 = 2%Z).
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
  - assert (Hf: Rfloor 1.1369261836552624 = 1%Z).
    {
      unfold Rfloor.
      assert (H: up 1.1369261836552624 = 2%Z).
      {
        symmetry.
        apply tech_up; simpl; lra.
      }
      rewrite H.
      reflexivity.
    }
    rewrite Hf.
    simpl.
    lra.
  - lra.
Qed.