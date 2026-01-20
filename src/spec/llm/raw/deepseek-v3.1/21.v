
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.

Definition rescale_to_unit_spec (numbers : list R) (result : list R) : Prop :=
  length numbers >= 2 /\
  exists mi ma,
    mi = fold_left Rmin numbers (hd 0%R numbers) /\
    ma = fold_left Rmax numbers (hd 0%R numbers) /\
    mi <> ma /\
    result = map (λ x => (x - mi) * / (ma - mi)) numbers.
