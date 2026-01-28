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

Lemma floor_123_456 : Rfloor (123456/1000) = 123%Z.
Proof.
  unfold Rfloor.
  assert (H: up (123456/1000) = 124%Z).
  {
    symmetry.
    apply tech_up; simpl; lra.
  }
  rewrite H.
  reflexivity.
Qed.

Example test_problem_2 : problem_2_spec (123456/1000) (456/1000).
Proof.
  unfold problem_2_spec.
  split.
  - rewrite floor_123_456.
    simpl.
    lra.
  - lra.
Qed.