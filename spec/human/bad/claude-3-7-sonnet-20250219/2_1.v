Require Import Reals.
Require Import Micromega.Lra.
Open Scope R_scope.

Definition problem_2_pre(x : R) : Prop :=
  x > 0.

Definition floor (x : R) : Z :=
  let z := up x in (z - 1)%Z.

Definition problem_2_spec (x frac : R) : Prop :=
  frac = x - IZR (floor x) /\
  0 <= frac < 1.

Lemma floor_3_5 : floor 3.5 = 3%Z.
Proof.
  unfold floor.
  assert (up 3.5 = 4%Z) by (apply tech_up; lra).
  rewrite H.
  reflexivity.
Qed.

Example test_problem_2 : problem_2_spec 3.5 0.5.
Proof.
  unfold problem_2_spec.
  split.
  - rewrite floor_3_5.
    simpl.
    lra.
  - split; lra.
Qed.