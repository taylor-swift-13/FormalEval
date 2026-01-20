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
  [-4; 301; 7; 3; 289; 290; 699; -8; 6; 2; 0; 8; 7; 2; 3; 3] 
  [-4; 301; 7; 2; 289; 290; 3; -8; 6; 3; 0; 8; 7; 2; 3; 699].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices preservation *)
      intros i H.
      (* We destruct i 16 times to cover all elements in the list *)
      do 16 (destruct i as [|i]; [ 
        try (exfalso; compute in H; congruence); 
        compute; reflexivity 
      | ]).
      (* For i >= 16, both are None *)
      compute. destruct i; reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        (* Target: [-4; 2; 3; 3; 7; 699] *)
        (* Source: [-4; 3; 699; 2; 7; 3] *)
        apply perm_skip.
        (* Move 2 to front *)
        change [3; 699; 2; 7; 3] with ([3; 699] ++ 2 :: [7; 3]).
        transitivity (2 :: [3; 699] ++ [7; 3]).
        2: apply (Permutation_middle _ [3; 699] [7; 3] 2).
        apply perm_skip.
        (* Move 3 to front *)
        simpl. apply perm_skip.
        (* Move 3 to front *)
        change [699; 7; 3] with ([699; 7] ++ 3 :: []).
        transitivity (3 :: [699; 7] ++ []).
        2: apply (Permutation_middle _ [699; 7] [] 3).
        apply perm_skip.
        (* Move 7 to front *)
        simpl.
        change [699; 7] with ([699] ++ 7 :: []).
        transitivity (7 :: [699] ++ []).
        2: apply (Permutation_middle _ [699] [] 7).
        apply perm_skip.
        (* Remaining *)
        simpl. apply Permutation_refl.
      * (* Sortedness *)
        simpl.
        apply Sorted_cons.
        { apply HdRel_cons. apply Z.leb_le. reflexivity. }
        apply Sorted_cons.
        { apply HdRel_cons. apply Z.leb_le. reflexivity. }
        apply Sorted_cons.
        { apply HdRel_cons. apply Z.leb_le. reflexivity. }
        apply Sorted_cons.
        { apply HdRel_cons. apply Z.leb_le. reflexivity. }
        apply Sorted_cons.
        { apply HdRel_cons. apply Z.leb_le. reflexivity. }
        apply Sorted_cons.
        { apply HdRel_nil. }
        apply Sorted_nil.
Qed.