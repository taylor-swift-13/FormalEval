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
  [4; -2; -12; 4; 23; 2; 3; 11; 12; -10; 4; -12] 
  [-12; -2; 3; 4; 4; 2; 4; 11; 12; -10; 23; -12].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 12 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* LHS: [4; -12; 23; 3; 12; 4] *)
        (* RHS: [-12; 3; 4; 4; 12; 23] *)
        
        (* Move -12 to front *)
        apply Permutation_trans with (l' := -12 :: [4; 23; 3; 12; 4]).
        { apply perm_swap. }
        apply perm_skip.
        
        (* Move 3 to front of [4; 23; 3; 12; 4] *)
        apply Permutation_trans with (l' := 3 :: [4; 23; 12; 4]).
        { apply Permutation_trans with (l' := 4 :: 3 :: [23; 12; 4]).
          - apply perm_skip. apply perm_swap.
          - apply perm_swap. }
        apply perm_skip.
        
        (* [4; 23; 12; 4] vs [4; 4; 12; 23] *)
        apply perm_skip.
        
        (* [23; 12; 4] vs [4; 12; 23] *)
        apply Permutation_trans with (l' := 4 :: [23; 12]).
        { apply Permutation_trans with (l' := 23 :: 4 :: [12]).
          - apply perm_skip. apply perm_swap.
          - apply perm_swap. }
        apply perm_skip.
        
        (* [23; 12] vs [12; 23] *)
        apply perm_swap.
        
      * (* 4. Sorted check *)
        simpl.
        apply Sorted_cons.
        { apply Sorted_cons.
          { apply Sorted_cons.
            { apply Sorted_cons.
              { apply Sorted_cons.
                { apply Sorted_cons.
                  { apply Sorted_nil. }
                  { apply HdRel_nil. } }
                { apply HdRel_cons. lia. } }
              { apply HdRel_cons. lia. } }
            { apply HdRel_cons. lia. } }
          { apply HdRel_cons. lia. } }
        { apply HdRel_cons. lia. }
Qed.