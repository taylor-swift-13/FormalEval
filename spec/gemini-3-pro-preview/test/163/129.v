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

Example test_case : generate_integers_spec 2 2 [2].
Proof.
  unfold generate_integers_spec.
  simpl Z.min. simpl Z.max.
  split.
  - repeat constructor.
  - intros x. split.
    + intros H_in.
      simpl in H_in.
      destruct H_in as [H | H].
      * rewrite <- H. split; [lia | split; [lia | reflexivity]].
      * contradiction.
    + intros [H_range [H_bound H_even]].
      assert (H_eq: x = 2) by lia.
      rewrite H_eq.
      simpl. left. reflexivity.
Qed.