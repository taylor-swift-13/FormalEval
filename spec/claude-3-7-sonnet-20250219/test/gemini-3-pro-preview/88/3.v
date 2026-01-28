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

Example test_sort_array_1 : sort_array_spec [2; 4; 3; 0; 1; 5] [0; 1; 2; 3; 4; 5].
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
        simpl in H.
        repeat (destruct i as [|i]; [| try lia]).
        all: repeat (destruct j as [|j]; [| try lia]).
        all: simpl; lia.
    + intros x.
      simpl.
      intuition.
Qed.