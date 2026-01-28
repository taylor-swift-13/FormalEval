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

Example test_case : generate_integers_spec 16 987654324 [].
Proof.
  unfold generate_integers_spec.
  split.
  - (* Prove Sorted Z.lt [] *)
    constructor.
  - (* Prove the logical equivalence *)
    intros x. split.
    + (* Forward direction: In list -> satisfies conditions *)
      intros H_in.
      inversion H_in.
    + (* Backward direction: satisfies conditions -> In list *)
      intros [H_range [H_bound H_even]].
      destruct H_range as [H_ge H_le].
      (* Calculate lower bound to show contradiction with x < 10 *)
      assert (H_min: Z.min 16 987654324 = 16) by reflexivity.
      rewrite H_min in H_ge.
      (* 16 <= x and x < 10 is a contradiction *)
      lia.
Qed.