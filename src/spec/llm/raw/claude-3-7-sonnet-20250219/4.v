
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Definition mean_absolute_deviation_spec (numbers : list R) (mad : R) : Prop :=
  length numbers > 0 /\
  let mean := (fold_right Rplus 0 numbers) / INR (length numbers) in
  mad = (fold_right Rplus 0 (map (fun x => Rabs (x - mean)) numbers)) / INR (length numbers).
