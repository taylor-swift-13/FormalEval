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

Lemma floor_0_77 : forall x : R, 0 < x < 1 -> Rfloor x = 0%Z.
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

Example test_problem_2 : forall x : R, 
  x = 0.7713842427275083 -> 
  problem_2_spec x x.
Proof.
  intros x Hx.
  unfold problem_2_spec.
  split.
  - assert (Hfloor: Rfloor x = 0%Z).
    {
      apply floor_0_77.
      rewrite Hx.
      lra.
    }
    rewrite Hfloor.
    simpl.
    lra.
  - rewrite Hx.
    lra.
Qed.