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
  [300; 500; 6; 7; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; 5; 700; 900; -901; 800; 1000; -277] 
  [-277; 500; 6; 3; 290; 8; 7; 20; -105; 289; 104; 200; 300; 4; 5; 700; 900; -901; 800; 1000; -277].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* We verify indices 0 to 20 explicitly using destruct to avoid large computations *)
      do 21 (destruct i as [|i]; [
        simpl in *;
        try reflexivity;
        exfalso; compute in H; apply H; reflexivity
      | ]).
      (* For i >= 21, both lists return None *)
      simpl. reflexivity.
    + split.
      * simpl.
        (* Manual permutation proof for the extracted elements *)
        (* Target (sorted): [-277; 3; 7; 289; 300; 700; 800] *)
        (* Source (original): [300; 7; 289; -277; 3; 700; 800] *)
        
        (* Move -277 to front *)
        transitivity (-277 :: [300; 7; 289] ++ [3; 700; 800]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        (* Move 3 to front *)
        transitivity (3 :: [300; 7; 289] ++ [700; 800]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        (* Move 7 to front *)
        transitivity (7 :: [300] ++ [289; 700; 800]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        (* Move 289 to front *)
        transitivity (289 :: [300] ++ [700; 800]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        (* Remaining elements [300; 700; 800] are already in order *)
        apply Permutation_refl.
        
      * simpl.
        (* Verify sortedness of the resulting list *)
        repeat (constructor; [ compute; discriminate | ]).
        apply Sorted_nil.
Qed.