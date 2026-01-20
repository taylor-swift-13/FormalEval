Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition generate_integers_spec (a b : Z) (l : list Z) : Prop :=
  let lower := Z.min a b in
  let upper := Z.max a b in
  Sorted Z.lt l /\
  (forall x : Z, In x l <-> lower <= x <= upper /\ x < 10 /\ Z.even x = true).

Example test_case : generate_integers_spec 987654321 18 [].
Proof.
  unfold generate_integers_spec.
  split.
  - constructor.
  - intros x. split.
    + intros H. inversion H.
    + intros [H_range [H_bound _]].
      lia.
Qed.