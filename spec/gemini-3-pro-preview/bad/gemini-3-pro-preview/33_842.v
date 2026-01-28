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
  [-7; 6; 7; 290; 8; 289; 104; -277; 200; 3; 4; -8; 700; -2; -901; 800; 1000; 1000] 
  [-7; 6; 7; 3; 8; 289; 104; -277; 200; 290; 4; -8; 700; -2; -901; 800; 1000; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 18 (destruct i; [
        simpl in H; 
        try (contradict H; discriminate); 
        simpl; reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * cbv [extract_thirds Nat.modulo Nat.eqb].
        apply perm_skip.
        transitivity (3 :: [290; 104] ++ [700; 800]).
        -- simpl. apply perm_skip.
           apply perm_swap.
        -- assert (H: [290; 104; 3; 700; 800] = [290; 104] ++ 3 :: [700; 800]) by reflexivity.
           rewrite H.
           apply Permutation_middle.
      * cbv [extract_thirds Nat.modulo Nat.eqb].
        repeat (apply Sorted_cons; [
          try apply HdRel_nil;
          apply HdRel_cons;
          apply Z.leb_le; reflexivity
        | ]).
        apply Sorted_nil.
Qed.