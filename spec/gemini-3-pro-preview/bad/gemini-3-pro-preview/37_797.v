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
  [5; 3; -5; -3; 3; -2; -9; 0; 6; -2; -10] 
  [-10; 3; -9; -3; -5; -2; 3; 0; 5; -2; 6].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 12 (destruct i as [|i]; 
             [ simpl in Hodd; try discriminate; simpl; try reflexivity 
             | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with (l' := 5 :: [-10; -9; -5; 3; 6]).
        2: { replace ([-10; -9; -5; 3; 5; 6]) with ([-10; -9; -5; 3] ++ 5 :: [6]) by reflexivity.
             apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        
        apply Permutation_trans with (l' := -5 :: [-10; -9; 3; 6]).
        2: { replace ([-10; -9; -5; 3; 6]) with ([-10; -9] ++ -5 :: [3; 6]) by reflexivity.
             apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        
        apply Permutation_trans with (l' := 3 :: [-10; -9; 6]).
        2: { replace ([-10; -9; 3; 6]) with ([-10; -9] ++ 3 :: [6]) by reflexivity.
             apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        
        apply Permutation_trans with (l' := -9 :: [-10; 6]).
        2: { replace ([-10; -9; 6]) with ([-10] ++ -9 :: [6]) by reflexivity.
             apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        
        apply Permutation_trans with (l' := 6 :: [-10]).
        2: { replace ([-10; 6]) with ([-10] ++ 6 :: []) by reflexivity.
             apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | try (apply HdRel_cons; lia); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.