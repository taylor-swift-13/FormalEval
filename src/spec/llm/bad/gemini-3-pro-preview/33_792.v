Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.Morphisms.
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
  [300; 6; 7; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; 700; -901; 800; 1000; 104; 3] 
  [3; 6; 7; 4; 8; 289; 20; -105; -277; 104; 200; 3; 290; 700; -901; 300; 1000; 104; 800].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* preservation of non-thirds *)
      intros i H.
      do 19 (destruct i as [|i]; [ simpl in *; try (exfalso; lia); try reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        change [300; 290; 20; 104; 4; 800; 3] with ([300; 290; 20; 104; 4; 800] ++ 3 :: []).
        rewrite <- Permutation_middle. apply Permutation_cons.
        change [300; 290; 20; 104; 4; 800] with ([300; 290; 20; 104] ++ 4 :: [800]).
        rewrite <- Permutation_middle. apply Permutation_cons.
        change [300; 290; 20; 104; 800] with ([300; 290] ++ 20 :: [104; 800]).
        rewrite <- Permutation_middle. apply Permutation_cons.
        change [300; 290; 104; 800] with ([300; 290] ++ 104 :: [800]).
        rewrite <- Permutation_middle. apply Permutation_cons.
        change [300; 290; 800] with ([300] ++ 290 :: [800]).
        rewrite <- Permutation_middle. apply Permutation_cons.
        change [300; 800] with ([] ++ 300 :: [800]).
        rewrite <- Permutation_middle. apply Permutation_cons.
        apply Permutation_refl.
      * (* Sorted *)
        simpl.
        repeat (constructor; [| simpl; try lia]).
        apply Sorted_nil.
Qed.