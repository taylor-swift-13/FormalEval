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

Example test_sort_even_case : sort_even_spec [2; 3; 2; 9; 3; 6; 7; 8; -10; 2; 2; 3; 3] [-10; 3; 2; 9; 2; 6; 2; 8; 3; 2; 3; 3; 7].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 13 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        (* Goal: Permutation [2; 2; 3; 7; -10; 2; 3] [-10; 2; 2; 2; 3; 3; 7] *)
        (* Move -10 (index 4) to front *)
        eapply Permutation_trans.
        { do 3 apply Permutation_skip. apply Permutation_swap. }
        eapply Permutation_trans.
        { do 2 apply Permutation_skip. apply Permutation_swap. }
        eapply Permutation_trans.
        { apply Permutation_skip. apply Permutation_swap. }
        eapply Permutation_trans.
        { apply Permutation_swap. }
        apply Permutation_cons.
        
        (* Goal: Permutation [2; 2; 3; 7; 2; 3] [2; 2; 2; 3; 3; 7] *)
        apply Permutation_cons.
        apply Permutation_cons.
        
        (* Goal: Permutation [3; 7; 2; 3] [2; 3; 3; 7] *)
        (* Move 2 (index 2) to front *)
        eapply Permutation_trans.
        { apply Permutation_skip. apply Permutation_swap. }
        eapply Permutation_trans.
        { apply Permutation_swap. }
        apply Permutation_cons.
        
        (* Goal: Permutation [3; 7; 3] [3; 3; 7] *)
        apply Permutation_cons.
        
        (* Goal: Permutation [7; 3] [3; 7] *)
        apply Permutation_swap.
      
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; simpl; lia) ]).
        apply Sorted_nil.
Qed.