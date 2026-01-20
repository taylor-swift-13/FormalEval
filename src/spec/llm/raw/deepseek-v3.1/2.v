
Require Import Coq.Reals.Reals.

Definition truncate_number_spec (number : R) (result : R) : Prop :=
  result = number - IZR (Int_part number).
