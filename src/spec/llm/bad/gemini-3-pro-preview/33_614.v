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
  [300; 500; 6; 289; 290; 8; 289; 20; 104; -277; 104; 200; -8; 700; 900; -901; 800; 1000; 15; -8; 700] 
  [-901; 500; 6; -277; 290; 8; -8; 20; 104; 15; 104; 200; 289; 700; 900; 289; 800; 1000; 300; -8; 700].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      repeat (destruct i; [
        simpl; try reflexivity;
        try (exfalso; apply H; reflexivity)
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_trans with (l' := -901 :: [300; 289; 289; -277; -8; 15]).
        { change [300; 289; 289; -277; -8; -901; 15] with ([300; 289; 289; -277; -8] ++ -901 :: [15]).
          apply Permutation_sym, Permutation_middle. }
        apply Permutation_cons.
        
        apply Permutation_trans with (l' := -277 :: [300; 289; 289; -8; 15]).
        { change [300; 289; 289; -277; -8; 15] with ([300; 289; 289] ++ -277 :: [-8; 15]).
          apply Permutation_sym, Permutation_middle. }
        apply Permutation_cons.

        apply Permutation_trans with (l' := -8 :: [300; 289; 289; 15]).
        { change [300; 289; 289; -8; 15] with ([300; 289; 289] ++ -8 :: [15]).
          apply Permutation_sym, Permutation_middle. }
        apply Permutation_cons.

        apply Permutation_trans with (l' := 15 :: [300; 289; 289]).
        { change [300; 289; 289; 15] with ([300; 289; 289] ++ 15 :: []).
          apply Permutation_sym, Permutation_middle. }
        apply Permutation_cons.

        apply Permutation_trans with (l' := 289 :: [300; 289]).
        { change [300; 289; 289] with ([300] ++ 289 :: [289]).
          apply Permutation_sym, Permutation_middle. }
        apply Permutation_cons.

        apply Permutation_trans with (l' := 289 :: [300]).
        { change [300; 289] with ([300] ++ 289 :: []).
          apply Permutation_sym, Permutation_middle. }
        apply Permutation_cons.
        
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | constructor; try (apply Z.leb_le; vm_compute; reflexivity) ]).
        apply Sorted_nil.
Qed.