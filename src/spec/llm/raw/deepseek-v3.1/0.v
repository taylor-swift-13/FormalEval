
Require Import List.
Require Import ZArith.
Require Import Bool.

Definition has_close_elements_spec (numbers : list float) (threshold : float) (result : bool) : Prop :=
  exists sorted_numbers : list float,
    Permutation numbers sorted_numbers /\
    StronglySorted (fun x y => x <= y) sorted_numbers /\
    (result = true <-> exists i : nat, 
        i < length sorted_numbers - 1 /\
        (nth i sorted_numbers 0.0) - (nth (i + 1) sorted_numbers 0.0) < threshold).
