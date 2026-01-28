Require Import Reals.
Require Import Psatz.
Require Import ZArith.
Open Scope R_scope.
Open Scope Z_scope.

Definition truncate_number (x : R) : R :=
  x - IZR (Int_part x).

Definition problem_2_pre(x : R) : Prop :=
  x > 0.

Definition problem_2_spec (x frac : R) : Prop :=
  frac = x - IZR (Int_part x) /\
  0 <= frac < 1.

Lemma Int_part_correct : forall x, 0 <= x - IZR (Int_part x) < 1.
Proof.
  intros x.
  unfold Rminus.
  split.
  - apply Rle_Rminus.
    apply archimed.
  - apply Rlt_Rminus.
    apply archimed.
Qed.

Example test_case : problem_2_spec 3.5 0.5.
Proof.
  unfold problem_2_spec.
  split.
  - unfold truncate_number.
    simpl.
    reflexivity.
  - apply Int_part_correct.
Qed.

Qed.