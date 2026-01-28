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
  [5; 2; 7; -1; 9; 0; 3; -6; 9; 7; 11; 8; -6; 0; 300; 1; 13; 6; -2; 19]
  [-6; 2; 7; -2; 9; 0; -1; -6; 9; 1; 11; 8; 3; 0; 300; 5; 13; 6; 7; 19].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      repeat (destruct i as [|i]; 
        [ simpl in *; 
          try (match goal with | [ H : (0 <> 0)%nat |- _ ] => contradiction H end);
          try reflexivity; 
          try (exfalso; compute in H; congruence)
        | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-6; -2; -1; 1; 3; 5; 7] [5; -1; 3; 7; -6; 1; -2] *)
        transitivity (-6 :: [5; -1; 3; 7; 1; -2]).
        2: { change [5; -1; 3; 7; -6; 1; -2] with ([5; -1; 3; 7] ++ -6 :: [1; -2]). 
             apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        transitivity (-2 :: [5; -1; 3; 7; 1]).
        2: { change [5; -1; 3; 7; 1; -2] with ([5; -1; 3; 7; 1] ++ -2 :: []). 
             apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.

        transitivity (-1 :: [5; 3; 7; 1]).
        2: { change [5; -1; 3; 7; 1] with ([5] ++ -1 :: [3; 7; 1]). 
             apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.

        transitivity (1 :: [5; 3; 7]).
        2: { change [5; 3; 7; 1] with ([5; 3; 7] ++ 1 :: []). 
             apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.

        transitivity (3 :: [5; 7]).
        2: { change [5; 3; 7] with ([5] ++ 3 :: [7]). 
             apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.

        transitivity (5 :: [7]).
        2: { change [5; 7] with ([] ++ 5 :: [7]). 
             apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.

        apply Permutation_refl.

      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; apply HdRel_cons; simpl; trivial ]).
        apply Sorted_nil.
Qed.