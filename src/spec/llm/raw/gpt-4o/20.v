
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Init.Nat.

Definition find_closest_elements_spec (numbers : list R) (result : R * R) : Prop :=
  length numbers >= 2 /\
  let sorted_numbers := sort Rle numbers in
  exists min_diff,
    (forall l r, In l sorted_numbers -> In r sorted_numbers -> l <> r -> Rabs (fst result - snd result) <= Rabs (l - r)) /\
    result = (fst result, snd result) /\
    fst result < snd result /\
    In (fst result) sorted_numbers /\
    In (snd result) sorted_numbers.
