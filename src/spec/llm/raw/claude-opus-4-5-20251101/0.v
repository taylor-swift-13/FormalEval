
Require Import Reals.
Require Import List.
Require Import Bool.
Import ListNotations.

Open Scope R_scope.

Definition has_close_elements_spec (numbers : list R) (threshold : R) (result : bool) : Prop :=
  result = true <->
  exists (i j : nat) (x y : R),
    i < length numbers /\
    j < length numbers /\
    i <> j /\
    nth_error numbers i = Some x /\
    nth_error numbers j = Some y /\
    Rabs (x - y) < threshold.
