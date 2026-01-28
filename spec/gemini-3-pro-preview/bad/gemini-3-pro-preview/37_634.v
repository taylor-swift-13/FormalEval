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
  [5; 3; 10; -5; 2; -3; 3; -9; 0; 123; 1; 10] 
  [0; 3; 1; -5; 2; -3; 3; -9; 5; 123; 10; 10].
Proof.
  unfold sort_even_spec.
  split.
  - (* Length *)
    simpl. reflexivity.
  - split.
    + (* Odd indices *)
      intros i Hlen Hodd.
      (* Check indices 0 to 11 *)
      do 12 (destruct i; [ try (simpl in Hodd; discriminate); try reflexivity | ]).
      (* Remaining indices >= 12 *)
      simpl in Hlen. lia.
    + split.
      * (* Permutation *)
        simpl.
        (* Goal: Permutation [5; 10; 2; 3; 0; 1] [0; 1; 2; 3; 5; 10] *)
        
        (* Move 0 to front *)
        assert (H0: Permutation [5; 10; 2; 3; 0; 1] (0 :: [5; 10; 2; 3; 1])).
        { change [5; 10; 2; 3; 0; 1] with ([5; 10; 2; 3] ++ 0 :: [1]). apply Permutation_sym, Permutation_middle. }
        etransitivity; [apply H0 |]. clear H0. apply Permutation_cons.
        
        (* Move 1 to front *)
        assert (H1: Permutation [5; 10; 2; 3; 1] (1 :: [5; 10; 2; 3])).
        { change [5; 10; 2; 3; 1] with ([5; 10; 2; 3] ++ 1 :: []). apply Permutation_sym, Permutation_middle. }
        etransitivity; [apply H1 |]. clear H1. apply Permutation_cons.
        
        (* Move 2 to front *)
        assert (H2: Permutation [5; 10; 2; 3] (2 :: [5; 10; 3])).
        { change [5; 10; 2; 3] with ([5; 10] ++ 2 :: [3]). apply Permutation_sym, Permutation_middle. }
        etransitivity; [apply H2 |]. clear H2. apply Permutation_cons.
        
        (* Move 3 to front *)
        assert (H3: Permutation [5; 10; 3] (3 :: [5; 10])).
        { change [5; 10; 3] with ([5; 10] ++ 3 :: []). apply Permutation_sym, Permutation_middle. }
        etransitivity; [apply H3 |]. clear H3. apply Permutation_cons.
        
        (* 5 and 10 are already in order *)
        apply Permutation_cons.
        apply Permutation_refl.
      * (* Sorted *)
        simpl.
        repeat apply Sorted_cons.
        all: try apply HdRel_cons; try apply HdRel_nil; try apply Sorted_nil; try lia.
Qed.