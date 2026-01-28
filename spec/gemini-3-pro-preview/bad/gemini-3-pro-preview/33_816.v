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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 4; 5; 700; -104; -200; -104; -901; 800; 1000; 289]
  [-901; 500; 6; -104; 8; 289; 4; -105; -277; 7; 200; 3; 20; 5; 700; 104; -200; -104; 289; 800; 1000; 300].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length *)
    simpl. reflexivity.
  - split.
    + (* 2. indices *)
      intros i H.
      do 22 (destruct i; [ simpl in *; try congruence; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation *)
        simpl.
        (* Goal: Permutation (sorted) (original) *)
        (* We reorder original to match sorted step by step *)
        apply Permutation_sym.
        
        (* Move -901 to front *)
        transitivity (-901 :: [300; 7; 20; 104; 4; -104] ++ [289]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply perm_skip.
        
        (* Move -104 *)
        transitivity (-104 :: [300; 7; 20; 104; 4] ++ [289]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply perm_skip.
        
        (* Move 4 *)
        transitivity (4 :: [300; 7; 20; 104] ++ [289]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply perm_skip.
        
        (* Move 7 *)
        transitivity (7 :: [300] ++ [20; 104; 289]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply perm_skip.
        
        (* Move 20 *)
        transitivity (20 :: [300] ++ [104; 289]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply perm_skip.
        
        (* Move 104 *)
        transitivity (104 :: [300] ++ [289]).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply perm_skip.
        
        (* Move 289 *)
        transitivity (289 :: [300] ++ []).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply perm_skip.
        
        (* 300 remains *)
        apply Permutation_refl.
        
      * (* 4. Sorted *)
        simpl.
        repeat (apply Sorted_cons; [ constructor; simpl; try congruence | ]).
        apply Sorted_nil.
Qed.