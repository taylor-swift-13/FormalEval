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

Example test_mad : mean_absolute_deviation_spec [-1; -2; -3; 4; 5] 3.12.
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 5) with 5 by (simpl; lra).
  simpl sum_R.
  replace (-1 + (-2 + (-3 + (4 + (5 + 0))))) with 3 by lra.
  replace (3 / 5) with 0.6 by lra.
  simpl map.
  simpl sum_R.
  replace (-1 - 0.6) with (-1.6) by lra.
  replace (-2 - 0.6) with (-2.6) by lra.
  replace (-3 - 0.6) with (-3.6) by lra.
  replace (4 - 0.6) with 3.4 by lra.
  replace (5 - 0.6) with 4.4 by lra.
  replace (Rabs (-1.6)) with 1.6 by (unfold Rabs; destruct (Rcase_abs (-1.6)); lra).
  replace (Rabs (-2.6)) with 2.6 by (unfold Rabs; destruct (Rcase_abs (-2.6)); lra).
  replace (Rabs (-3.6)) with 3.6 by (unfold Rabs; destruct (Rcase_abs (-3.6)); lra).
  replace (Rabs 3.4) with 3.4 by (unfold Rabs; destruct (Rcase_abs 3.4); lra).
  replace (Rabs 4.4) with 4.4 by (unfold Rabs; destruct (Rcase_abs 4.4); lra).
  lra.
Qed.