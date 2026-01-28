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
  [1; 2; 3; 5; 1; 0; -8; 9; -12; 7; 6; 6; 1; 104; -13; 9] 
  [-8; 2; 3; 1; 1; 0; 1; 9; -12; 5; 6; 6; 7; 104; -13; 9].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length *)
    simpl. reflexivity.
  - split.
    + (* 2. indices *)
      intros i H.
      do 16 (destruct i; [ simpl in *; try congruence; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation *)
        simpl.
        (* Goal: Permutation [-8; 1; 1; 5; 7; 9] [1; 5; -8; 7; 1; 9] *)
        apply Permutation_trans with (l' := -8 :: [1; 5; 7; 1; 9]).
        -- apply perm_skip.
           (* Goal: Permutation [1; 1; 5; 7; 9] [1; 5; 7; 1; 9] *)
           apply perm_skip.
           (* Goal: Permutation [1; 5; 7; 9] [5; 7; 1; 9] *)
           change [5; 7; 1; 9] with ([5; 7] ++ 1 :: [9]).
           apply Permutation_middle.
        -- change [1; 5; -8; 7; 1; 9] with ([1; 5] ++ -8 :: [7; 1; 9]).
           apply Permutation_middle.
      * (* 4. Sorted *)
        simpl.
        repeat constructor; simpl; try lia.
Qed.