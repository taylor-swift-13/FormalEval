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
  [300; 500; 6; 7; 290; 8; 289; 20; -105; -3; 104; 200; 3; 4; 700; 900; -901; 800; 1000; -901; 290] 
  [-3; 500; 6; 3; 290; 8; 7; 20; -105; 289; 104; 200; 300; 4; 700; 900; -901; 800; 1000; -901; 290].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      do 21 (destruct i; [ simpl in *; try (contradict H; discriminate); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-3; 3; 7; 289; 300; 900; 1000] [300; 7; 289; -3; 3; 900; 1000] *)
        
        (* Move -3 to front of RHS *)
        assert (H1: Permutation [300; 7; 289; -3; 3; 900; 1000] (-3 :: [300; 7; 289] ++ [3; 900; 1000])).
        { replace [300; 7; 289; -3; 3; 900; 1000] with ([300; 7; 289] ++ -3 :: [3; 900; 1000]) by reflexivity.
          apply Permutation_sym. apply Permutation_middle. }
        etransitivity. 2: apply H1. clear H1.
        apply perm_skip.
        
        (* Move 3 to front of RHS *)
        assert (H2: Permutation [300; 7; 289; 3; 900; 1000] (3 :: [300; 7; 289] ++ [900; 1000])).
        { replace [300; 7; 289; 3; 900; 1000] with ([300; 7; 289] ++ 3 :: [900; 1000]) by reflexivity.
          apply Permutation_sym. apply Permutation_middle. }
        etransitivity. 2: apply H2. clear H2.
        apply perm_skip.

        (* Move 7 to front of RHS *)
        assert (H3: Permutation [300; 7; 289; 900; 1000] (7 :: [300] ++ [289; 900; 1000])).
        { replace [300; 7; 289; 900; 1000] with ([300] ++ 7 :: [289; 900; 1000]) by reflexivity.
          apply Permutation_sym. apply Permutation_middle. }
        etransitivity. 2: apply H3. clear H3.
        apply perm_skip.

        (* Swap 289 and 300 *)
        apply perm_swap.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; apply HdRel_cons; vm_compute; congruence ]).
        apply Sorted_nil.
Qed.