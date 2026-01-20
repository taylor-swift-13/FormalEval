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

Example test_sort_even_case : 
  sort_even_spec 
    [5; 3; -5; -4; 2; -3; 3; -9; 0; 123; 1; -10; 123] 
    [-5; 3; 0; -4; 1; -3; 2; -9; 3; 123; 5; -10; 123].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Verify each index 0..12 *)
      do 13 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      (* If i >= 13, length check fails *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* LHS evens: [5; -5; 2; 3; 0; 1; 123] *)
        (* RHS evens: [-5; 0; 1; 2; 3; 5; 123] *)
        
        (* Move -5 to front *)
        transitivity (-5 :: [5; 2; 3; 0; 1; 123]).
        { apply Permutation_sym. apply (Permutation_middle Z [5] [2;3;0;1;123] (-5)). }
        simpl. apply perm_skip.
        
        (* Move 0 to front *)
        transitivity (0 :: [5; 2; 3; 1; 123]).
        { apply Permutation_sym. apply (Permutation_middle Z [5; 2; 3] [1; 123] 0). }
        simpl. apply perm_skip.
        
        (* Move 1 to front *)
        transitivity (1 :: [5; 2; 3; 123]).
        { apply Permutation_sym. apply (Permutation_middle Z [5; 2; 3] [123] 1). }
        simpl. apply perm_skip.
        
        (* Move 2 to front *)
        transitivity (2 :: [5; 3; 123]).
        { apply Permutation_sym. apply (Permutation_middle Z [5] [3; 123] 2). }
        simpl. apply perm_skip.
        
        (* Move 3 to front *)
        transitivity (3 :: [5; 123]).
        { apply Permutation_sym. apply (Permutation_middle Z [5] [123] 3). }
        simpl. apply perm_skip.
        
        (* Head is 5, matches *)
        apply perm_skip.
        
        (* Tail is [123], matches *)
        apply Permutation_refl.
        
      * (* 4. Sorted check *)
        simpl.
        repeat (constructor; try lia).
Qed.