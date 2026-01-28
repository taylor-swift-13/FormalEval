Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
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

Example test_sort_array_1 : sort_array_spec [30; 2; 20; 10; 5] [2; 5; 10; 20; 30].
Proof.
  unfold sort_array_spec.
  right.
  split.
  - simpl. lia.
  - split.
    + simpl. left. split.
      * reflexivity.
      * unfold sorted_asc. intros i j [H1 H2].
        assert (Hi: i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
        assert (Hj: j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4) by lia.
        destruct Hi as [-> | [-> | [-> | [-> | ->]]]];
        destruct Hj as [-> | [-> | [-> | [-> | ->]]]];
        simpl; try lia.
    + intros x. simpl. split; intro H; repeat destruct H as [H|H]; subst; auto; try contradiction.
Qed.