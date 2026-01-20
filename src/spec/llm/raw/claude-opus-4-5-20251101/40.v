
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition triples_sum_to_zero_spec (l : list Z) (result : bool) : Prop :=
  result = true <->
  exists i j k : nat,
    i < length l /\
    j < length l /\
    k < length l /\
    i <> j /\
    i <> k /\
    j <> k /\
    exists a b c : Z,
      nth_error l i = Some a /\
      nth_error l j = Some b /\
      nth_error l k = Some c /\
      a + b + c = 0.
