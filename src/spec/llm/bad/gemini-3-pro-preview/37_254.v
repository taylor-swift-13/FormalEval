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
  [5; 3; -5; -4; 2; -3; 3; -10; 0; 123; 1; -10; 123] 
  [-5; 3; 0; -4; 1; -3; 2; -10; 3; 123; 5; -10; 123].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 13 (destruct i as [|i]; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Target: [-5; 0; 1; 2; 3; 5; 123] *)
        (* Current: [5; -5; 2; 3; 0; 1; 123] *)
        
        (* Move -5 to front *)
        assert (H1: Permutation [5; -5; 2; 3; 0; 1; 123] (-5 :: [5; 2; 3; 0; 1; 123])).
        { apply Permutation_sym. simpl. apply perm_swap. }
        rewrite H1. apply perm_skip. clear H1.
        
        (* Move 0 to front *)
        assert (H2: Permutation [5; 2; 3; 0; 1; 123] (0 :: [5; 2; 3; 1; 123])).
        { apply Permutation_sym. change [5; 2; 3; 0; 1; 123] with ([5; 2; 3] ++ 0 :: [1; 123]). apply Permutation_middle. }
        rewrite H2. apply perm_skip. clear H2.
        
        (* Move 1 to front *)
        assert (H3: Permutation [5; 2; 3; 1; 123] (1 :: [5; 2; 3; 123])).
        { apply Permutation_sym. change [5; 2; 3; 1; 123] with ([5; 2; 3] ++ 1 :: [123]). apply Permutation_middle. }
        rewrite H3. apply perm_skip. clear H3.
        
        (* Move 2 to front *)
        assert (H4: Permutation [5; 2; 3; 123] (2 :: [5; 3; 123])).
        { apply Permutation_sym. change [5; 2; 3; 123] with ([5] ++ 2 :: [3; 123]). apply Permutation_middle. }
        rewrite H4. apply perm_skip. clear H4.
        
        (* Move 3 to front (swap 5 and 3) *)
        apply perm_swap.
        apply perm_skip.
        
        (* 5 and 123 match *)
        apply Permutation_refl.
        
      * (* 4. Sorted check *)
        simpl.
        apply Sorted_cons. apply HdRel_cons. lia.
        apply Sorted_cons. apply HdRel_cons. lia.
        apply Sorted_cons. apply HdRel_cons. lia.
        apply Sorted_cons. apply HdRel_cons. lia.
        apply Sorted_cons. apply HdRel_cons. lia.
        apply Sorted_cons. apply HdRel_cons. lia.
        apply Sorted_cons. apply HdRel_nil.
        apply Sorted_nil.
Qed.