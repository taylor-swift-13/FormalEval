Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
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
  [500; 6; 7; -2; 8; 289; 20; -105; -277; 104; 200; 3; 4; 11; 700; -200; -901; 800; 1000; -277] 
  [-200; 6; 7; -2; 8; 289; 4; -105; -277; 20; 200; 3; 104; 11; 700; 500; -901; 800; 1000; -277].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* index preservation *)
      intros i H.
      (* Check the first 20 indices explicitly *)
      do 20 (destruct i as [|i]; [ simpl in *; try congruence; reflexivity | ]).
      (* For i >= 20, both lists are exhausted *)
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        (* Goal: Permutation [-200; -2; 4; 20; 104; 500; 1000] [500; -2; 20; 104; 4; -200; 1000] *)
        apply Permutation_sym.
        (* Goal: Permutation [500; -2; 20; 104; 4; -200; 1000] [-200; -2; 4; 20; 104; 500; 1000] *)
        (* Sort by moving elements to the front one by one *)
        transitivity (-200 :: [500; -2; 20; 104; 4; 1000]).
        { change [500; -2; 20; 104; 4; -200; 1000] with ([500; -2; 20; 104; 4] ++ -200 :: [1000]).
          apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        transitivity (-2 :: [500; 20; 104; 4; 1000]).
        { change [500; -2; 20; 104; 4; 1000] with ([500] ++ -2 :: [20; 104; 4; 1000]).
          apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        transitivity (4 :: [500; 20; 104; 1000]).
        { change [500; 20; 104; 4; 1000] with ([500; 20; 104] ++ 4 :: [1000]).
          apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        transitivity (20 :: [500; 104; 1000]).
        { change [500; 20; 104; 1000] with ([500] ++ 20 :: [104; 1000]).
          apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        transitivity (104 :: [500; 1000]).
        { change [500; 104; 1000] with ([500] ++ 104 :: [1000]).
          apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_refl.
      * (* Sorted *)
        simpl.
        repeat (constructor; simpl; try (intros H; discriminate)).
Qed.