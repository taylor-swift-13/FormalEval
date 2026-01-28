Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Lra.
Import ListNotations.
Open Scope R_scope.

Fixpoint sum_R (l : list R) : R :=
  match l with
  | [] => 0
  | h :: t => h + sum_R t
  end.

Definition mean_absolute_deviation_spec (numbers : list R) (result : R) : Prop :=
  let len := INR (length numbers) in
  let mean := sum_R numbers / len in
  let diffs := map (fun x => Rabs (x - mean)) numbers in
  result = sum_R diffs / len.

Example test_mad : mean_absolute_deviation_spec [-1; -2; -3; 5] 2.625.
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 4) with 4 by (simpl; lra).
  simpl sum_R.
  replace (-1 + (-2 + (-3 + (5 + 0)))) with (-1) by lra.
  simpl map.
  simpl sum_R.
  replace (-1 - -1 / 4) with (-0.75) by lra.
  replace (-2 - -1 / 4) with (-1.75) by lra.
  replace (-3 - -1 / 4) with (-2.75) by lra.
  replace (5 - -1 / 4) with 5.25 by lra.
  replace (Rabs (-0.75)) with 0.75 by (unfold Rabs; destruct (Rcase_abs (-0.75)); lra).
  replace (Rabs (-1.75)) with 1.75 by (unfold Rabs; destruct (Rcase_abs (-1.75)); lra).
  replace (Rabs (-2.75)) with 2.75 by (unfold Rabs; destruct (Rcase_abs (-2.75)); lra).
  replace (Rabs 5.25) with 5.25 by (unfold Rabs; destruct (Rcase_abs 5.25); lra).
  lra.
Qed.