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
  [300; 500; 6; 104; 7; 8; 289; 20; -105; -277; 104; 8; 9; 3; 9; 5; 700; 900; -200; -901; 800; 1000; -105] 
  [-277; 500; 6; -200; 7; 8; 5; 20; -105; 9; 104; 8; 104; 3; 9; 289; 700; 900; 300; -901; 800; 1000; -105].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      do 23 (destruct i; [
        simpl in *; try reflexivity; try (exfalso; apply H; reflexivity)
      | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Target: [-277; -200; 5; 9; 104; 289; 300; 1000] *)
        (* Source: [300; 104; 289; -277; 9; 5; -200; 1000] *)
        
        (* Move -277 to front *)
        apply Permutation_trans with (l' := -277 :: [300; 104; 289; 9; 5; -200; 1000]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        (* Move -200 to front *)
        apply Permutation_trans with (l' := -200 :: [300; 104; 289; 9; 5; 1000]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        (* Move 5 to front *)
        apply Permutation_trans with (l' := 5 :: [300; 104; 289; 9; 1000]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        (* Move 9 to front *)
        apply Permutation_trans with (l' := 9 :: [300; 104; 289; 1000]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        (* Move 104 to front *)
        apply Permutation_trans with (l' := 104 :: [300; 289; 1000]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        (* Move 289 to front *)
        apply Permutation_trans with (l' := 289 :: [300; 1000]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        (* 300 and 1000 are already aligned *)
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_nil.
        
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [
          try apply HdRel_nil;
          try (apply HdRel_cons; simpl; vm_compute; intro H; discriminate)
        | ]).
        apply Sorted_nil.
Qed.