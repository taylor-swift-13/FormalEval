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

Example test_mad : mean_absolute_deviation_spec [10.0; 10.0; 10.0; 10.0; 9.232092283615625] 0.245730469243.
Proof.
  unfold mean_absolute_deviation_spec.
  simpl.
  unfold Rabs.
  repeat match goal with
  | [ |- context[Rcase_abs ?x] ] => destruct (Rcase_abs x); try lra
  end.
Qed.