Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.

Open Scope R_scope.

Definition sum_list (l : list R) : R := fold_right Rplus 0 l.

Definition mean_absolute_deviation_spec (numbers : list R) (mad : R) : Prop :=
  length numbers <> 0 ->
  let mean := sum_list numbers / INR (length numbers) in
  mad = sum_list (map (fun x => Rabs (x - mean)) numbers) / INR (length numbers).