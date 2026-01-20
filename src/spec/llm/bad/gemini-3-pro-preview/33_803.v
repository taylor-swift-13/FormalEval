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
  [300; 500; 6; 7; 290; 8; 289; 20; 104; -277; 8; 104; 200; -8; 700; 900; -901; 800; 1000; 290; -8; 104; 1000]
  [-277; 500; 6; 7; 290; 8; 104; 20; 104; 200; 8; 104; 289; -8; 700; 300; -901; 800; 900; 290; -8; 1000; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. Length *)
    simpl. reflexivity.
  - split.
    + (* 2. Indices *)
      intros i H.
      do 23 (destruct i as [|i]; [
        try (compute in H; congruence);
        vm_compute; reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation *)
        simpl.
        apply Permutation_trans with (l' := -277 :: [300; 7; 289] ++ [200; 900; 1000; 104]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        
        apply Permutation_trans with (l' := 7 :: [300] ++ [289; 200; 900; 1000; 104]).
        2: apply Permutation_middle.
        apply Permutation_cons.

        apply Permutation_trans with (l' := 104 :: [300; 289; 200; 900; 1000] ++ []).
        2: apply Permutation_middle.
        apply Permutation_cons.

        apply Permutation_trans with (l' := 200 :: [300; 289] ++ [900; 1000]).
        2: apply Permutation_middle.
        apply Permutation_cons.

        apply Permutation_trans with (l' := 289 :: [300] ++ [900; 1000]).
        2: apply Permutation_middle.
        apply Permutation_cons.

        apply Permutation_trans with (l' := 300 :: [] ++ [900; 1000]).
        2: apply Permutation_middle.
        apply Permutation_cons.

        apply Permutation_trans with (l' := 900 :: [] ++ [1000]).
        2: apply Permutation_middle.
        apply Permutation_cons.

        apply Permutation_refl.
      * (* 4. Sorted *)
        simpl.
        repeat (apply Sorted_cons; [
          simpl; auto with zarith |
        ]).
        apply Sorted_nil.
Qed.