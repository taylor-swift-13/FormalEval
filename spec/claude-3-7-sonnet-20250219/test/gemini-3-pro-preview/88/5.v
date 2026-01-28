Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Require Import Coq.micromega.Lia.

Definition sorted_asc (l : list nat) : Prop :=
  forall i j, i < j < length l -> nth i l 0 <= nth j l 0.

Definition sorted_desc (l : list nat) : Prop :=
  forall i j, i < j < length l -> nth i l 0 >= nth j l 0.

Definition sort_array_spec (array result : list nat) : Prop :=
  (array = [] /\ result = []) \/
  (length array > 0 /\
   (let sum := hd 0 array + last array 0 in
    (Nat.odd sum = true /\ sorted_asc result) \/
    (Nat.odd sum = false /\ sorted_desc result)) /\
   forall x, In x result <-> In x array).

Example test_sort_array_1 : sort_array_spec [2; 1] [1; 2].
Proof.
  unfold sort_array_spec.
  right.
  split.
  - simpl. lia.
  - split.
    + simpl.
      left.
      split.
      * reflexivity.
      * unfold sorted_asc.
        intros i j H.
        simpl in H. destruct H as [Hi Hj].
        destruct i.
        -- destruct j.
           ++ lia.
           ++ destruct j; simpl; try lia.
        -- simpl in Hj. lia.
    + intros x. simpl. intuition.
Qed.