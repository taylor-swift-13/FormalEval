Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Micromega.Lia.
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
  [1; 2; 3; -3; 1; 5; 2; 11; 0; -8; 105; 9; -12; 7; 6; 2; -3] 
  [-12; 2; 3; -8; 1; 5; -3; 11; 0; 1; 105; 9; 2; 7; 6; 2; -3].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check all indices up to the length of the list *)
      do 17 (destruct i; [ simpl in *; try reflexivity; try (exfalso; lia) | ]).
      (* For indices beyond the list length, both are None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* LHS: [-12; -8; -3; 1; 2; 2] *)
        (* RHS: [1; -3; 2; -8; -12; 2] *)
        
        (* Move -12 to front *)
        transitivity (-12 :: [1; -3; 2; -8] ++ [2]).
        2: apply Permutation_cons_app.
        apply Permutation_cons.
        
        (* Move -8 to front *)
        transitivity (-8 :: [1; -3; 2] ++ [2]).
        2: apply Permutation_cons_app.
        apply Permutation_cons.
        
        (* Move -3 to front *)
        transitivity (-3 :: [1] ++ [2; 2]).
        2: apply Permutation_cons_app.
        apply Permutation_cons.
        
        (* Remaining lists match *)
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; cbv; intro Hc; discriminate Hc) ]).
        apply Sorted_nil.
Qed.