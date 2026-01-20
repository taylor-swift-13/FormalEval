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
  [5; -6; 2; -3; 3; 0; -9; 0; 1; -10; 10; 2] 
  [-9; -6; 1; -3; 2; 0; 3; 0; 5; -10; 10; 2].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 12 (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        apply Permutation_trans with (l' := -9 :: [5; 2; 3; 1; 10]).
        { apply Permutation_sym. apply (Permutation_middle _ [5; 2; 3] [1; 10] (-9)). }
        apply perm_skip.
        
        apply Permutation_trans with (l' := 1 :: [5; 2; 3; 10]).
        { apply Permutation_sym. apply (Permutation_middle _ [5; 2; 3] [10] 1). }
        apply perm_skip.
        
        apply Permutation_trans with (l' := 2 :: [5; 3; 10]).
        { apply Permutation_sym. apply (Permutation_middle _ [5] [3; 10] 2). }
        apply perm_skip.
        
        apply Permutation_trans with (l' := 3 :: [5; 10]).
        { apply Permutation_sym. apply (Permutation_middle _ [5] [10] 3). }
        apply perm_skip.
        
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; first [ apply HdRel_cons; lia | apply HdRel_nil ] ]).
        apply Sorted_nil.
Qed.