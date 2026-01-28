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
  [1; 2; 3; 5; 1; 0; -8; 9; -12; 7; 6; 6; 1] 
  [-8; 2; 3; 1; 1; 0; 1; 9; -12; 5; 6; 6; 7].
Proof.
  unfold sort_third_spec.
  split.
  - (* Length *)
    simpl. reflexivity.
  - split.
    + (* Indices not divisible by 3 *)
      intros i H.
      (* Iterate through indices 0 to 12 *)
      do 13 (destruct i; [ simpl in *; try reflexivity; try congruence | ]).
      (* For i >= 13 *)
      simpl. reflexivity.
    + split.
      * (* Permutation of thirds *)
        simpl.
        (* Goal: Permutation [-8; 1; 1; 5; 7] [1; 5; -8; 7; 1] *)
        apply Permutation_sym.
        (* Goal: Permutation [1; 5; -8; 7; 1] [-8; 1; 1; 5; 7] *)
        
        (* Move -8 to the front *)
        change [1; 5; -8; 7; 1] with ([1; 5] ++ -8 :: [7; 1]).
        eapply Permutation_trans.
        1: { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply perm_skip.
        
        (* Goal: Permutation [1; 5; 7; 1] [1; 1; 5; 7] *)
        apply perm_skip.
        
        (* Goal: Permutation [5; 7; 1] [1; 5; 7] *)
        (* Move 1 to the front *)
        change [5; 7; 1] with ([5; 7] ++ 1 :: nil).
        eapply Permutation_trans.
        1: { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply perm_skip.
        
        apply Permutation_refl.
      * (* Sortedness *)
        simpl.
        repeat constructor; compute; congruence.
Qed.