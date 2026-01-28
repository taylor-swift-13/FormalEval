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
  [5; 4; 4; 5; 0; 3; 8; 8; 0; 5; 4] 
  [0; 4; 0; 5; 4; 3; 4; 8; 5; 5; 8].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 11 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with ([0; 5; 4; 8; 0; 4]).
        { apply Permutation_sym. apply Permutation_cons_app with (l1 := [5; 4]) (l2 := [8; 0; 4]). apply Permutation_refl. }
        simpl. apply perm_skip.
        apply Permutation_trans with ([0; 5; 4; 8; 4]).
        { apply Permutation_sym. apply Permutation_cons_app with (l1 := [5; 4; 8]) (l2 := [4]). apply Permutation_refl. }
        simpl. apply perm_skip.
        apply Permutation_trans with ([4; 5; 8; 4]).
        { apply Permutation_sym. apply Permutation_cons_app with (l1 := [5]) (l2 := [8; 4]). apply Permutation_refl. }
        simpl. apply perm_skip.
        apply Permutation_trans with ([4; 5; 8]).
        { apply Permutation_sym. apply Permutation_cons_app with (l1 := [5; 8]) (l2 := []). apply Permutation_refl. }
        simpl. apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_nil; try apply HdRel_cons; lia]).
        apply Sorted_nil.
Qed.