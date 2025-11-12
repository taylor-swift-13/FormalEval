
Require Import List.
Require Import ZArith.
Require Import Reals.

Definition mean_absolute_deviation_spec (numbers : list R) (result : R) : Prop :=
  exists mean : R,
  mean = (sum_list_R numbers) / (INR (length numbers)) /\
  result = (sum_list_R (map (fun x => Rabs (x - mean)) numbers)) / (INR (length numbers)).
