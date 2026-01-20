
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition pairs_sum_to_zero_spec (l : list Z) (result : bool) : Prop :=
  result = true <->
  exists i j : nat,
    i < length l /\
    j < length l /\
    i <> j /\
    exists vi vj : Z,
      nth_error l i = Some vi /\
      nth_error l j = Some vj /\
      vi + vj = 0.
