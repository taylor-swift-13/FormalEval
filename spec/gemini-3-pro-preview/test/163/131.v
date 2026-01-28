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

Example test_case : generate_integers_spec 10000 10000 [].
Proof.
  unfold generate_integers_spec.
  simpl Z.min. simpl Z.max.
  split.
  - (* Prove Sorted Z.lt [] *)
    constructor.
  - (* Prove the logical equivalence *)
    intros x. split.
    + (* Forward direction: In [] -> ... *)
      intros H. inversion H.
    + (* Backward direction: satisfies conditions -> In [] *)
      intros [H_range [H_bound H_even]].
      (* H_range: 10000 <= x <= 10000 implies x = 10000 *)
      (* H_bound: x < 10 *)
      (* Contradiction: 10000 < 10 is false *)
      lia.
Qed.