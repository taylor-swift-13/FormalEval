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
  [300; 6; 7; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; 700; 900; 700; -901; 800; -901; 20; 3; 6; 8; 8]
  [-901; 6; 7; 4; 8; 289; 6; -105; -277; 20; 200; 3; 104; 700; 900; 290; -901; 800; 300; 20; 3; 700; 8; 8].
Proof.
  unfold sort_third_spec.
  split.
  - (* length res = length l *)
    reflexivity.
  - split.
    + (* Preservation of indices not divisible by 3 *)
      intros i H.
      (* Since the list length is 24, we check indices 0 to 23 explicitly. *)
      do 24 (destruct i; [ 
        simpl; try reflexivity; try (exfalso; apply H; reflexivity) 
      | ]).
      (* For i >= 24, both nth_error return None *)
      simpl. reflexivity.
    + split.
      * (* Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-901; 4; 6; 20; 104; 290; 300; 700] [300; 290; 20; 104; 4; 700; -901; 6] *)
        (* We reorder the right list to match the left using transitivity and swap/middle *)
        
        (* Move -901 *)
        replace [300; 290; 20; 104; 4; 700; -901; 6] 
           with ([300; 290; 20; 104; 4; 700] ++ -901 :: [6]) by reflexivity.
        transitivity (-901 :: [300; 290; 20; 104; 4; 700] ++ [6]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons. simpl.
        
        (* Move 4 *)
        replace [300; 290; 20; 104; 4; 700; 6] 
           with ([300; 290; 20; 104] ++ 4 :: [700; 6]) by reflexivity.
        transitivity (4 :: [300; 290; 20; 104] ++ [700; 6]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons. simpl.

        (* Move 6 *)
        replace [300; 290; 20; 104; 700; 6] 
           with ([300; 290; 20; 104; 700] ++ 6 :: []) by reflexivity.
        transitivity (6 :: [300; 290; 20; 104; 700] ++ []).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons. simpl.

        (* Move 20 *)
        replace [300; 290; 20; 104; 700] 
           with ([300; 290] ++ 20 :: [104; 700]) by reflexivity.
        transitivity (20 :: [300; 290] ++ [104; 700]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons. simpl.

        (* Move 104 *)
        replace [300; 290; 104; 700] 
           with ([300; 290] ++ 104 :: [700]) by reflexivity.
        transitivity (104 :: [300; 290] ++ [700]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons. simpl.

        (* Move 290 *)
        replace [300; 290; 700] 
           with ([300] ++ 290 :: [700]) by reflexivity.
        transitivity (290 :: [300] ++ [700]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons. simpl.

        (* Remaining matches *)
        apply Permutation_refl.

      * (* Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ 
          simpl; try (apply HdRel_cons; lia); try apply HdRel_nil 
        | ]).
        apply Sorted_nil.
Qed.