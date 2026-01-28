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

Example test_sort_array_1 : sort_array_spec [7; 9; 11; 11] [11; 11; 9; 7].
Proof.
  unfold sort_array_spec.
  right.
  split.
  - simpl; lia.
  - split.
    + simpl.
      right.
      split.
      * reflexivity.
      * unfold sorted_desc.
        intros i j [H_lt H_len].
        destruct i.
        { (* i = 0 *)
          destruct j; [lia|].
          destruct j; [simpl; lia|].
          destruct j; [simpl; lia|].
          destruct j; [simpl; lia|].
          simpl in H_len; lia.
        }
        destruct i.
        { (* i = 1 *)
          destruct j; [lia|].
          destruct j; [lia|].
          destruct j; [simpl; lia|].
          destruct j; [simpl; lia|].
          simpl in H_len; lia.
        }
        destruct i.
        { (* i = 2 *)
          destruct j; [lia|].
          destruct j; [lia|].
          destruct j; [lia|].
          destruct j; [simpl; lia|].
          simpl in H_len; lia.
        }
        simpl in H_len; lia.
    + intros x.
      simpl.
      split; intro H; repeat destruct H as [H|H]; subst; auto.
Qed.