
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope Z_scope.

Definition count_up_to_spec (n : Z) (ans : list Z) : Prop :=
  Sorted Z.lt ans /\
  (forall x : Z, In x ans <-> (Z.prime x /\ x < n)).
