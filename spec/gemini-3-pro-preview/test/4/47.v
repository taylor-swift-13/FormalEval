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

Example test_mad : mean_absolute_deviation_spec [1; 1; 2; 2; 2] 0.48.
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 5) with 5 by (simpl; lra).
  simpl sum_R.
  replace (1 + (1 + (2 + (2 + (2 + 0))))) with 8 by lra.
  replace (8 / 5) with 1.6 by lra.
  simpl map.
  simpl sum_R.
  replace (1 - 1.6) with (-0.6) by lra.
  replace (2 - 1.6) with 0.4 by lra.
  replace (Rabs (-0.6)) with 0.6 by (unfold Rabs; destruct (Rcase_abs (-0.6)); lra).
  replace (Rabs 0.4) with 0.4 by (unfold Rabs; destruct (Rcase_abs 0.4); lra).
  lra.
Qed.