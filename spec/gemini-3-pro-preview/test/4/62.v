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

Example test_mad : mean_absolute_deviation_spec [-2.0; 2.0; 10.416066198571809] 4.629362754920804.
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 3) with 3 by (simpl; lra).
  simpl sum_R.
  replace (-2.0 + (2.0 + (10.416066198571809 + 0))) with 10.416066198571809 by lra.
  simpl map.
  simpl sum_R.
  replace (Rabs (-2.0 - 10.416066198571809 / 3)) with (10.416066198571809 / 3 + 2.0) by (unfold Rabs; destruct (Rcase_abs (-2.0 - 10.416066198571809 / 3)); lra).
  replace (Rabs (2.0 - 10.416066198571809 / 3)) with (10.416066198571809 / 3 - 2.0) by (unfold Rabs; destruct (Rcase_abs (2.0 - 10.416066198571809 / 3)); lra).
  replace (Rabs (10.416066198571809 - 10.416066198571809 / 3)) with (10.416066198571809 - 10.416066198571809 / 3) by (unfold Rabs; destruct (Rcase_abs (10.416066198571809 - 10.416066198571809 / 3)); lra).
  lra.
Qed.