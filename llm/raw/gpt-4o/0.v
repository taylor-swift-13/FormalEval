
Require Import List.
Require Import Reals.

Definition has_close_elements_spec (numbers : list R) (threshold : R) (result : bool) : Prop :=
  (exists i j, 0 <= i < j < length numbers /\ Rabs (nth i numbers 0 - nth j numbers 0) < threshold) <-> result = true.
