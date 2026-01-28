Require Import Reals.
Require Import ZArith.
Open Scope R_scope.

Definition problem_2_pre(x : R) : Prop :=
  x > 0.

Definition problem_2_spec (x frac : R) : Prop :=
  frac = x - IZR (Int_part x) /\
  0 <= frac < 1.

Lemma int_part_prop : forall x : R, IZR (Int_part x) <= x < IZR (Int_part x + 1).
Proof.
  intro x.
  split.
  - apply archimed.
  - apply Rlt_le_trans with (IZR (Int_part x) + 1).
    + apply archimed.
    + rewrite plus_IZR.
      apply Rplus_le_compat_l.
      apply Rle_refl.
Qed.

Example test_truncate : problem_2_spec 3.5 0.5.
Proof.
  unfold problem_2_spec.
  split.
  - unfold Int_part.
    simpl.
    lra.
  - split.
    + lra.
    + lra.
Qed.