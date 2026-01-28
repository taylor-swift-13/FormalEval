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

Example test_case : generate_integers_spec 123456790 56788 [].
Proof.
  unfold generate_integers_spec.
  split.
  - (* Prove Sorted Z.lt [] *)
    constructor.
  - (* Prove the logical equivalence *)
    intros x. split.
    + (* Forward direction: In [] -> satisfies conditions *)
      intros H. inversion H.
    + (* Backward direction: satisfies conditions -> In [] *)
      intros [H_range [H_bound H_even]].
      (* lower = 56788, upper = 123456790 *)
      (* H_range implies 56788 <= x *)
      (* H_bound implies x < 10 *)
      (* This is a contradiction *)
      lia.
Qed.