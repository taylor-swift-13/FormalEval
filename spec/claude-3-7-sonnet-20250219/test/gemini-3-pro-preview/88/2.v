Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.

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

Example test_sort_array_1 : sort_array_spec [5] [5].
Proof.
  unfold sort_array_spec.
  right.
  split.
  - simpl. apply Nat.lt_0_succ.
  - split.
    + simpl. right. split.
      * reflexivity.
      * unfold sorted_desc. intros i j H.
        simpl in H. destruct H as [H1 H2].
        destruct j.
        -- inversion H1.
        -- apply Nat.lt_1_r in H2. discriminate.
    + intros x. split; auto.
Qed.