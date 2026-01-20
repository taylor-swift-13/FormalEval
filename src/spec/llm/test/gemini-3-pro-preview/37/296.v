Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Fixpoint get_evens (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: [] => [x]
  | x :: _ :: tl => x :: get_evens tl
  end.

Definition sort_even_spec (l res : list Z) : Prop :=
  length l = length res /\
  (forall i : nat, (i < length l)%nat -> Nat.odd i = true -> nth i l 0 = nth i res 0) /\
  Permutation (get_evens l) (get_evens res) /\
  Sorted Z.le (get_evens res).

Example test_sort_even_case : sort_even_spec 
  [5; -13; 3; -5; 2; -10; -3; -2; 3; -8; 0; -10; -9; 2] 
  [-9; -13; -3; -5; 0; -10; 2; -2; 3; -8; 3; -10; 5; 2].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 14 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_cons_app with (l1 := [-9; -3; 0; 2; 3; 3]) (l2 := []).
        simpl.
        apply Permutation_cons_app with (l1 := [-9; -3; 0; 2]) (l2 := [3]).
        simpl.
        apply Permutation_cons_app with (l1 := [-9; -3; 0]) (l2 := [3]).
        simpl.
        apply Permutation_cons_app with (l1 := [-9]) (l2 := [0; 3]).
        simpl.
        apply Permutation_cons_app with (l1 := [-9; 0]) (l2 := []).
        simpl.
        apply Permutation_cons_app with (l1 := [-9]) (l2 := []).
        simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_cons; try apply HdRel_nil; try lia]).
        apply Sorted_nil.
Qed.