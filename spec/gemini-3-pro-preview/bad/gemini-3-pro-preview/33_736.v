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
  [500; 6; 7; 290; 8; 899; 20; -105; -277; 104; 200; 3; 4; 700; 900; -901; 291; 800; 1000; 105; 290] 
  [-901; 6; 7; 4; 8; 899; 20; -105; -277; 104; 200; 3; 290; 700; 900; 500; 291; 800; 1000; 105; 290].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 21 (destruct i; [ simpl in *; try (compute in H; congruence); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        eapply Permutation_trans with (l' := -901 :: [500; 290; 20; 104; 4] ++ [1000]).
        2: apply Permutation_middle.
        simpl. apply perm_skip.
        
        eapply Permutation_trans with (l' := 4 :: [500; 290; 20; 104] ++ [1000]).
        2: apply Permutation_middle.
        simpl. apply perm_skip.
        
        eapply Permutation_trans with (l' := 20 :: [500; 290] ++ [104; 1000]).
        2: apply Permutation_middle.
        simpl. apply perm_skip.
        
        eapply Permutation_trans with (l' := 104 :: [500; 290] ++ [1000]).
        2: apply Permutation_middle.
        simpl. apply perm_skip.
        
        eapply Permutation_trans with (l' := 290 :: [500] ++ [1000]).
        2: apply Permutation_middle.
        simpl. apply perm_skip.
        
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_nil; try (apply HdRel_cons; unfold Z.le; simpl; discriminate)]).
        apply Sorted_nil.
Qed.