
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Definition triples_sum_to_zero_spec (l : list Z) (result : bool) : Prop :=
  result = true <-> exists i j k,
    i <> j /\ i <> k /\ j <> k /\
    nth_error l i = Some (nth i l 0) /\
    nth_error l j = Some (nth j l 0) /\
    nth_error l k = Some (nth k l 0) /\
    nth i l 0 + nth j l 0 + nth k l 0 = 0.
