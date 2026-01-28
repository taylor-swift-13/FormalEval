Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Fixpoint extract_thirds (l : list Z) (i : nat) : list Z :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list Z) (res : list Z) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted Z.le (extract_thirds res 0).

Example test_case : sort_third_spec 
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; -8; 0; 5; 11; 900; 18; -901; 800; 1000; 0; -277; -277; 500] 
  [-277; 500; 6; 0; 8; 289; 7; -105; -277; 20; 200; -8; 104; 5; 11; 300; 18; -901; 800; 1000; 0; 900; -277; 500].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 24 (destruct i as [|i]; [ 
        simpl in *; 
        try (exfalso; apply H; reflexivity); 
        try reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        (* List: [300; 7; 20; 104; 0; 900; 800; -277] *)
        (* Target: [-277; 0; 7; 20; 104; 300; 800; 900] *)
        transitivity (-277 :: [300; 7; 20; 104; 0; 900; 800]).
        2: { change [300; 7; 20; 104; 0; 900; 800; -277] with ([300; 7; 20; 104; 0; 900; 800] ++ [-277]).
             apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        transitivity (0 :: [300; 7; 20; 104; 900; 800]).
        2: { change [300; 7; 20; 104; 0; 900; 800] with ([300; 7; 20; 104] ++ 0 :: [900; 800]).
             apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        transitivity (7 :: [300; 20; 104; 900; 800]).
        2: { change [300; 7; 20; 104; 900; 800] with ([300] ++ 7 :: [20; 104; 900; 800]).
             apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        transitivity (20 :: [300; 104; 900; 800]).
        2: { change [300; 20; 104; 900; 800] with ([300] ++ 20 :: [104; 900; 800]).
             apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        transitivity (104 :: [300; 900; 800]).
        2: { change [300; 104; 900; 800] with ([300] ++ 104 :: [900; 800]).
             apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- all: try apply HdRel_nil; try (apply HdRel_cons; lia).
Qed.