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

Example test_mad : mean_absolute_deviation_spec [-2; 2; 1.4955482911935327] (14.9910965823870654 / 9).
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 3) with 3 by (simpl; lra).
  simpl sum_R.
  replace (-2 + (2 + (1.4955482911935327 + 0))) with 1.4955482911935327 by lra.
  simpl map.
  simpl sum_R.
  replace (Rabs (-2 - 1.4955482911935327 / 3)) with (1.4955482911935327 / 3 + 2) by (unfold Rabs; destruct (Rcase_abs (-2 - 1.4955482911935327 / 3)); lra).
  replace (Rabs (2 - 1.4955482911935327 / 3)) with (2 - 1.4955482911935327 / 3) by (unfold Rabs; destruct (Rcase_abs (2 - 1.4955482911935327 / 3)); lra).
  replace (Rabs (1.4955482911935327 - 1.4955482911935327 / 3)) with (1.4955482911935327 - 1.4955482911935327 / 3) by (unfold Rabs; destruct (Rcase_abs (1.4955482911935327 - 1.4955482911935327 / 3)); lra).
  lra.
Qed.