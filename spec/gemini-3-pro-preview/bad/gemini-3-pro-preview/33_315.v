Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
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
  [-4; 7; 105; 3; 3; 0; 7; -8; -2; 2; 0; 1; 20; 0; 0; 0; 1] 
  [-4; 7; 105; 0; 3; 0; 2; -8; -2; 3; 0; 1; 7; 0; 0; 20; 1].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* We verify the condition for every index i. 
         Since the list has length 17, we destruct i 17 times. 
         For i >= 17, both nth_error return None. *)
      do 17 (destruct i as [|i]; [ 
        simpl in *; 
        try (exfalso; compute in H; congruence); 
        try reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        (* Prove Permutation [-4; 0; 2; 3; 7; 20] [-4; 3; 7; 2; 20; 0] *)
        apply Permutation_cons.
        transitivity (0 :: [3; 7; 2; 20]).
        -- apply Permutation_cons.
           (* Goal: Permutation [2; 3; 7; 20] [3; 7; 2; 20] *)
           change (2 :: [3; 7; 20]) with (2 :: [3; 7] ++ [20]).
           change ([3; 7; 2; 20]) with ([3; 7] ++ 2 :: [20]).
           apply Permutation_middle.
        -- (* Goal: Permutation (0 :: [3; 7; 2; 20]) [3; 7; 2; 20; 0] *)
           apply Permutation_middle.
      * simpl.
        repeat (apply Sorted_cons || apply Sorted_nil || (apply HdRel_cons; lia) || apply HdRel_nil).
Qed.