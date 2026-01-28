Require Import Reals.
Require Import ZArith.
Require Import Psatz.
Require Import Lia.
Require Import Coq.Logic.IndefiniteDescription.

Open Scope R_scope.
Open Scope Z_scope.

Definition problem_2_pre(x : R) : Prop :=
  x > 0.

(* Define floor using the Archimedean property and indefinite description *)
Definition floor (x : R) : Z :=
  proj1_sig (constructive_indefinite_description
               (fun z : Z => IZR z <= x < IZR z + 1)
               (archimed x)).

Lemma floor_spec : forall x : R, IZR (floor x) <= x < IZR (floor x) + 1.
Proof.
  intro x.
  unfold floor.
  destruct (constructive_indefinite_description
              (fun z : Z => IZR z <= x < IZR z + 1)
              (archimed x)) as [z Hz].
  simpl; exact Hz.
Qed.

Definition problem_2_spec (x frac : R) : Prop :=
  frac = x - IZR (floor x) /\
  0 <= frac < 1.

Example problem_2_pre_holds : problem_2_pre 3.5%R.
Proof.
  unfold problem_2_pre; lra.
Qed.

Lemma floor_35 : floor 3.5%R = 3%Z.
Proof.
  pose proof (floor_spec 3.5%R) as [Hlb Hub].
  assert (Hge3 : (3 <= floor 3.5)%Z).
  { assert (2.5%R < IZR (floor 3.5%R)) by lra.
    destruct (Z_le_gt_dec (floor 3.5%R) 2%Z) as [Hle2|Hgt2].
    - assert (IZR (floor 3.5%R) <= 2%R) by (apply IZR_le; exact Hle2).
      lra.
    - lia.
  }
  assert (Hle3 : (floor 3.5 <= 3)%Z).
  { destruct (Z_le_gt_dec 4%Z (floor 3.5%R)) as [Hge4|Hlt4].
    - assert (4%R <= IZR (floor 3.5%R)) by (apply IZR_le; exact Hge4).
      lra.
    - lia.
  }
  lia.
Qed.

Example problem_2_test : problem_2_spec 3.5%R 0.5%R.
Proof.
  unfold problem_2_spec.
  split.
  - rewrite floor_35.
    change (IZR 3%Z) with 3%R.
    lra.
  - lra.
Qed.