
Require Import List.
Require Import Reals.

Definition mean_absolute_deviation_spec (numbers : list R) (mad : R) : Prop :=
  let mean := (fold_right Rplus 0 numbers) / INR (length numbers) in
  mad = (fold_right Rplus 0 (map (fun x => Rabs (x - mean)) numbers)) / INR (length numbers).
