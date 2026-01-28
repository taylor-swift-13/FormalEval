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

Example test_mad : mean_absolute_deviation_spec [-2; 1; 1; 2; 2; 2] 1.
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 6) with 6 by (simpl; lra).
  simpl sum_R.
  replace (-2 + (1 + (1 + (2 + (2 + (2 + 0)))))) with 6 by lra.
  replace (6 / 6) with 1 by lra.
  simpl map.
  simpl sum_R.
  replace (-2 - 1) with (-3) by lra.
  replace (1 - 1) with 0 by lra.
  replace (2 - 1) with 1 by lra.
  replace (Rabs (-3)) with 3 by (unfold Rabs; destruct (Rcase_abs (-3)); lra).
  replace (Rabs 0) with 0 by (unfold Rabs; destruct (Rcase_abs 0); lra).
  replace (Rabs 1) with 1 by (unfold Rabs; destruct (Rcase_abs 1); lra).
  lra.
Qed.