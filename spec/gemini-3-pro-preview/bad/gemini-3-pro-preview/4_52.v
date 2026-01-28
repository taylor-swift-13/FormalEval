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

Example test_mad : mean_absolute_deviation_spec [7.5; -5.5; 10.416066198571809; 10.416066198571809; 10.416066198571809] 4.859855887657234.
Proof.
  unfold mean_absolute_deviation_spec.
  simpl length.
  replace (INR 5) with 5 by (simpl; lra).
  simpl sum_R.
  simpl map.
  simpl sum_R.
  unfold Rabs.
  repeat match goal with
  | [ |- context[Rcase_abs ?X] ] => destruct (Rcase_abs X); try lra
  end.
  lra.
Qed.