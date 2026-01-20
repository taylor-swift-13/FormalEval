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

Example test_case : generate_integers_spec 1 999 [2; 4; 6; 8].
Proof.
  unfold generate_integers_spec.
  simpl Z.min. simpl Z.max.
  split.
  - repeat constructor; try lia.
  - intros x. split.
    + intros H_in.
      simpl in H_in.
      destruct H_in as [H | [H | [H | [H | H]]]].
      * rewrite <- H. split; [lia | split; [lia | reflexivity]].
      * rewrite <- H. split; [lia | split; [lia | reflexivity]].
      * rewrite <- H. split; [lia | split; [lia | reflexivity]].
      * rewrite <- H. split; [lia | split; [lia | reflexivity]].
      * contradiction.
    + intros [H_range [H_bound H_even]].
      assert (H_enum: x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9) by lia.
      destruct H_enum as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]].
      * simpl in H_even. discriminate.
      * simpl. left. reflexivity.
      * simpl in H_even. discriminate.
      * simpl. right. left. reflexivity.
      * simpl in H_even. discriminate.
      * simpl. right. right. left. reflexivity.
      * simpl in H_even. discriminate.
      * simpl. right. right. right. left. reflexivity.
      * simpl in H_even. discriminate.
Qed.