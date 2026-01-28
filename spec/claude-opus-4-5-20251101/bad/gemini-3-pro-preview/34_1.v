Require Import List.
Require Import Sorting.
Require Import Permutation.
Require Import Arith.
Require Import Lia.

Import ListNotations.

Definition is_sorted (l : list nat) : Prop :=
  forall i j, i < j -> j < length l -> 
    nth i l 0 <= nth j l 0.

Definition no_duplicates (l : list nat) : Prop :=
  NoDup l.

Definition all_elements_from (result original : list nat) : Prop :=
  forall x, In x result <-> In x original.

Definition unique_spec (l : list nat) (result : list nat) : Prop :=
  is_sorted result /\
  no_duplicates result /\
  all_elements_from result l.

Example test_unique_sort : 
  unique_spec [5; 3; 5; 2; 3; 3; 9; 0; 123] [0; 2; 3; 5; 9; 123].
Proof.
  unfold unique_spec.
  split.
  - (* is_sorted *)
    unfold is_sorted. intros i j Hlt Hlen.
    simpl in Hlen.
    repeat (
      destruct i as [|i]; [
        repeat (destruct j as [|j]; [ lia | simpl; try lia ])
      | destruct j as [|j]; [ lia | simpl in *; apply lt_S_n in Hlt; apply le_S_n in Hlen ]
      ]
    ).
    lia.
  - split.
    + (* no_duplicates *)
      unfold no_duplicates.
      repeat (constructor; [ 
        intros H; simpl in H; repeat (destruct H as [H|H]; [lia|]); contradiction 
      | ]).
      auto.
    + (* all_elements_from *)
      unfold all_elements_from. intro x.
      split; intro H; simpl in H.
      * repeat (destruct H as [H|H]; [subst; simpl; auto 20 | ]); contradiction.
      * repeat (destruct H as [H|H]; [subst; simpl; auto 20 | ]); contradiction.
Qed.