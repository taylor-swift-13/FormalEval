
Require Import List.
Require Import Arith.
Require Import ZArith.
Open Scope Z_scope.

Definition maximum_spec (arr : list Z) (k : nat) (result : list Z) : Prop :=
  length result = k /\
  (forall x, In x result -> In x arr) /\
  (forall x y, In x result -> In y arr -> x >= y) /\
  Sorted Z.le result.
