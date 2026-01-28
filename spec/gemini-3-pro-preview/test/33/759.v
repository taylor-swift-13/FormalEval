Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
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
  [300; 500; 6; 7; 289; 20; -105; -277; 104; 200; 3; 4; 5; 700; 900; -200; -104; -901; 800; 1000; 5] 
  [-200; 500; 6; -105; 289; 20; 5; -277; 104; 7; 3; 4; 200; 700; 900; 300; -104; -901; 800; 1000; 5].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check for indices 0 to 20. For i > 20, both are None. *)
      do 21 (destruct i; [ simpl in *; try (exfalso; lia); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-200; -105; 5; 7; 200; 300; 800] [300; 7; -105; 200; 5; -200; 800] *)
        (* We match each element from the left in the right list and move it to the front *)
        
        (* Match -200 *)
        replace [300; 7; -105; 200; 5; -200; 800] with ([300; 7; -105; 200; 5] ++ -200 :: [800]) by reflexivity.
        apply Permutation_cons_app. simpl.
        
        (* Match -105 *)
        replace [300; 7; -105; 200; 5; 800] with ([300; 7] ++ -105 :: [200; 5; 800]) by reflexivity.
        apply Permutation_cons_app. simpl.
        
        (* Match 5 *)
        replace [300; 7; 200; 5; 800] with ([300; 7; 200] ++ 5 :: [800]) by reflexivity.
        apply Permutation_cons_app. simpl.
        
        (* Match 7 *)
        replace [300; 7; 200; 800] with ([300] ++ 7 :: [200; 800]) by reflexivity.
        apply Permutation_cons_app. simpl.
        
        (* Match 200 *)
        replace [300; 200; 800] with ([300] ++ 200 :: [800]) by reflexivity.
        apply Permutation_cons_app. simpl.
        
        (* Match 300 *)
        replace [300; 800] with ([] ++ 300 :: [800]) by reflexivity.
        apply Permutation_cons_app. simpl.
        
        (* Match 800 *)
        apply Permutation_refl.
        
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.