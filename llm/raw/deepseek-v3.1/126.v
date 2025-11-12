
Require Import List ZArith.
Import ListNotations.

Definition is_sorted_spec (lst : list Z) (result : bool) : Prop :=
  (forall x, count_occ Z.eq_dec lst x <= 2) /\
  (result = true <-> lst = sort Z.le lst) /\
  (forall x, In x lst -> x >= 0).
