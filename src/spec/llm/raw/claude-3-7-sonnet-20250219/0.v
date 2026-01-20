
Require Import List.
Import ListNotations.
Require Import Reals.
Open Scope R_scope.

Definition has_close_elements_spec (numbers : list R) (threshold : R) (result : bool) : Prop :=
  result = 
    (exists i j : nat,
      i < j < length numbers /\
      Rabs (nth i numbers 0 - nth j numbers 0) < threshold).
