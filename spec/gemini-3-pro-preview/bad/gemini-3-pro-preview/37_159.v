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
  [6; 3; 5; 1; 4; 1; 5; 9; 2; 6; 5; 3; 6] 
  [2; 3; 4; 1; 5; 1; 5; 9; 5; 6; 6; 3; 6].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 13 (destruct i; [ 
        simpl in Hodd; try discriminate Hodd; simpl; try reflexivity 
      | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        assert (H2: Permutation ([6; 5; 4; 5] ++ 2 :: [5; 6]) (2 :: [6; 5; 4; 5; 5; 6])).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl in H2. rewrite H2. apply perm_skip.
        
        assert (H4: Permutation ([6; 5] ++ 4 :: [5; 5; 6]) (4 :: [6; 5; 5; 5; 6])).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl in H4. rewrite H4. apply perm_skip.
        
        assert (H5: Permutation ([6] ++ 5 :: [5; 5; 6]) (5 :: [6; 5; 5; 6])).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl in H5. rewrite H5. apply perm_skip.
        
        assert (H5b: Permutation ([6] ++ 5 :: [5; 6]) (5 :: [6; 5; 6])).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl in H5b. rewrite H5b. apply perm_skip.
        
        assert (H5c: Permutation ([6] ++ 5 :: [6]) (5 :: [6; 6])).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl in H5c. rewrite H5c. apply perm_skip.
        
        apply Permutation_refl.
      * simpl.
        repeat constructor; lia.
Qed.