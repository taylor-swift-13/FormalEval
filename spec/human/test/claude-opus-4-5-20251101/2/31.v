Require Import Reals.
Require Import Lra.
Open Scope R_scope.

(* Define floor function for reals *)
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

Lemma floor_small_positive : forall x : R, 0 < x < 1 -> Rfloor x = 0%Z.
Proof.
  intros x [H1 H2].
  unfold Rfloor.
  assert (H: up x = 1%Z).
  {
    symmetry.
    apply tech_up; simpl; lra.
  }
  rewrite H.
  reflexivity.
Qed.

Example test_problem_2 : problem_2_spec (5907618779899971 / 100000000000000000) (5907618779899971 / 100000000000000000).
Proof.
  unfold problem_2_spec.
  split.
  - assert (Hfloor: Rfloor (5907618779899971 / 100000000000000000) = 0%Z).
    {
      apply floor_small_positive.
      lra.
    }
    rewrite Hfloor.
    simpl.
    lra.
  - lra.
Qed.