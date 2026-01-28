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
  [300; 6; 699; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; 700; 900; -901; 800; 19; 104; 3; -901]
  [-901; 6; 699; 4; 8; 289; 20; -105; -277; 104; 200; 3; 104; 700; 900; 290; 800; 19; 300; 3; -901].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check for all indices in range [0, 21] *)
      do 22 (destruct i; [
        try (vm_compute in H; congruence); (* if i mod 3 = 0, H is False *)
        vm_compute; reflexivity            (* if i mod 3 <> 0, check equality *)
      | ]).
      (* For i >= 22, both nth_error return None *)
      vm_compute. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        vm_compute.
        (* Goal: Permutation [sorted_thirds] [extracted_thirds] *)
        (* extracted_thirds = [300; 290; 20; 104; 4; -901; 104] *)
        (* sorted_thirds = [-901; 4; 20; 104; 104; 290; 300] *)
        apply Permutation_sym.
        
        (* Move -901 to front *)
        change ([300; 290; 20; 104; 4; -901; 104]) with ([300; 290; 20; 104; 4] ++ -901 :: [104]).
        apply Permutation_trans with (-901 :: [300; 290; 20; 104; 4] ++ [104]).
        { apply Permutation_sym; apply Permutation_middle. }
        apply Permutation_cons. simpl.
        
        (* Move 4 to front *)
        change ([300; 290; 20; 104; 4; 104]) with ([300; 290; 20; 104] ++ 4 :: [104]).
        apply Permutation_trans with (4 :: [300; 290; 20; 104] ++ [104]).
        { apply Permutation_sym; apply Permutation_middle. }
        apply Permutation_cons. simpl.

        (* Move 20 to front *)
        change ([300; 290; 20; 104; 104]) with ([300; 290] ++ 20 :: [104; 104]).
        apply Permutation_trans with (20 :: [300; 290] ++ [104; 104]).
        { apply Permutation_sym; apply Permutation_middle. }
        apply Permutation_cons. simpl.

        (* Move 104 to front *)
        change ([300; 290; 104; 104]) with ([300; 290] ++ 104 :: [104]).
        apply Permutation_trans with (104 :: [300; 290] ++ [104]).
        { apply Permutation_sym; apply Permutation_middle. }
        apply Permutation_cons. simpl.

        (* Move 104 to front *)
        change ([300; 290; 104]) with ([300; 290] ++ 104 :: []).
        apply Permutation_trans with (104 :: [300; 290] ++ []).
        { apply Permutation_sym; apply Permutation_middle. }
        apply Permutation_cons. simpl.

        (* Move 290 to front *)
        change ([300; 290]) with ([300] ++ 290 :: []).
        apply Permutation_trans with (290 :: [300] ++ []).
        { apply Permutation_sym; apply Permutation_middle. }
        apply Permutation_cons. simpl.

        (* Last element 300 *)
        apply Permutation_refl.

      * (* 4. Sortedness of extracted thirds *)
        vm_compute.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.