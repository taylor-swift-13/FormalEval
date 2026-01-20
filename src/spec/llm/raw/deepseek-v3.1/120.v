
Require Import List ZArith.
Import ListNotations.

Definition maximum_spec (arr : list Z) (k : nat) (result : list Z) : Prop :=
  length arr >= 1 /\ length arr <= 1000 /\
  (forall x, In x arr -> -1000 <= x <= 1000) /\
  0 <= k <= length arr /\
  result = firstn k (rev (sort Z.le arr)) /\
  sorted Z.le result.
