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

Lemma floor_0_999999 : Rfloor (999999/1000000) = 0%Z.
Proof.
  unfold Rfloor.
  assert (H: up (999999/1000000) = 1%Z).
  {
    symmetry.
    apply tech_up; simpl; lra.
  }
  rewrite H.
  reflexivity.
Qed.

Example test_problem_2 : problem_2_spec (999999/1000000) (999999/1000000).
Proof.
  unfold problem_2_spec.
  split.
  - rewrite floor_0_999999.
    simpl.
    lra.
  - lra.
Qed.