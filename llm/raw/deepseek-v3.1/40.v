
Require Import List ZArith.
Import ListNotations.

Definition triples_sum_to_zero_spec (l : list Z) : Prop :=
  exists i j k : nat, 
    i < length l /\ j < length l /\ k < length l /\
    i <> j /\ i <> k /\ j <> k /\
    nth i l 0 + nth j l 0 + nth k l 0 = 0.
