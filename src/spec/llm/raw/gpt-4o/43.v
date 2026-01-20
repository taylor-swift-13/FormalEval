
Require Import List.
Require Import Bool.
Require Import ZArith.

Definition pairs_sum_to_zero_spec (l : list Z) (result : bool) : Prop :=
  result = true <-> exists i j, i <> j /\ nth_error l i = Some (nth j l 0) /\ nth_error l j = Some (- nth i l 0).
