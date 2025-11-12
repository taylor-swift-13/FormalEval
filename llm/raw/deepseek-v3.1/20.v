
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Psatz.

Definition find_closest_elements_spec (numbers : list R) (result : R * R) : Prop :=
  length numbers >= 2 /\
  exists l r, result = (l, r) /\
  l <= r /\
  In l numbers /\ In r numbers /\
  (forall x y, In x numbers -> In y numbers -> x <> y -> Rabs (y - x) >= Rabs (r - l)).
