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

Example test_mad : mean_absolute_deviation_spec [-1; 4.5; 0; 2.5; -3; -5.5] 2.75.
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 6) with 6 by (simpl; lra).
  simpl sum_R.
  replace (-1 + (4.5 + (0 + (2.5 + (-3 + (-5.5 + 0)))))) with (-2.5) by lra.
  replace (-2.5 / 6) with (-5/12) by lra.
  simpl map.
  simpl sum_R.
  replace (-1 - -5 / 12) with (-7/12) by lra.
  replace (4.5 - -5 / 12) with (59/12) by lra.
  replace (0 - -5 / 12) with (5/12) by lra.
  replace (2.5 - -5 / 12) with (35/12) by lra.
  replace (-3 - -5 / 12) with (-31/12) by lra.
  replace (-5.5 - -5 / 12) with (-61/12) by lra.
  replace (Rabs (-7 / 12)) with (7/12) by (unfold Rabs; destruct (Rcase_abs (-7 / 12)); lra).
  replace (Rabs (59 / 12)) with (59/12) by (unfold Rabs; destruct (Rcase_abs (59 / 12)); lra).
  replace (Rabs (5 / 12)) with (5/12) by (unfold Rabs; destruct (Rcase_abs (5 / 12)); lra).
  replace (Rabs (35 / 12)) with (35/12) by (unfold Rabs; destruct (Rcase_abs (35 / 12)); lra).
  replace (Rabs (-31 / 12)) with (31/12) by (unfold Rabs; destruct (Rcase_abs (-31 / 12)); lra).
  replace (Rabs (-61 / 12)) with (61/12) by (unfold Rabs; destruct (Rcase_abs (-61 / 12)); lra).
  lra.
Qed.