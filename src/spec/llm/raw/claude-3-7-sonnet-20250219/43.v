
Require Import List.
Import ListNotations.
Require Import ZArith.
Open Scope Z_scope.

Definition pairs_sum_to_zero_spec (l : list Z) (b : bool) : Prop :=
  b = true <-> exists i j : nat,
    i < length l /\ j < length l /\
    i <> j /\
    nth i l 0 + nth j l 0 = 0.
