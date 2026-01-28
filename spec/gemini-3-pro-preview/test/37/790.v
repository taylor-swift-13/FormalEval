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
  [2; 3; 2; 9; 3; 6; 7; 8; -10; 2; 2; 3] 
  [-10; 3; 2; 9; 2; 6; 2; 8; 3; 2; 7; 3].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 12 (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Current: [2; 2; 3; 7; -10; 2], Target: [-10; 2; 2; 2; 3; 7] *)
        
        (* Move -10 to front *)
        assert (H1: Permutation [2; 2; 3; 7; -10; 2] (-10 :: [2; 2; 3; 7] ++ [2])).
        { change [2; 2; 3; 7; -10; 2] with ([2; 2; 3; 7] ++ -10 :: [2]). 
          apply Permutation_sym. apply Permutation_middle. }
        etransitivity; [ apply H1 | ]. clear H1.
        simpl. constructor.
        
        (* Current: [2; 2; 3; 7; 2], Target: [2; 2; 2; 3; 7] *)
        constructor. constructor.
        
        (* Current: [3; 7; 2], Target: [2; 3; 7] *)
        (* Move 2 to front *)
        assert (H2: Permutation [3; 7; 2] (2 :: [3; 7] ++ [])).
        { change [3; 7; 2] with ([3; 7] ++ 2 :: []). 
          apply Permutation_sym. apply Permutation_middle. }
        etransitivity; [ apply H2 | ]. clear H2.
        simpl. constructor.
        
        (* Current: [3; 7], Target: [3; 7] *)
        apply Permutation_refl.
        
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.