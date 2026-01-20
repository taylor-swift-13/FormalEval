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
  [19; 0; -901; 2; 3; 4; 5; 6; 7; 8; 10; 11; 9; 12; 13; 14; 15; 16; 17; 18; 19; 21; 20; 0] 
  [2; 0; -901; 5; 3; 4; 8; 6; 7; 9; 10; 11; 14; 12; 13; 17; 15; 16; 19; 18; 19; 21; 20; 0].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      do 24 (destruct i; [ simpl in *; try contradiction; try reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* LHS: [19; 2; 5; 8; 9; 14; 17; 21] *)
        (* RHS: [2; 5; 8; 9; 14; 17; 19; 21] *)
        change [2; 5; 8; 9; 14; 17; 19; 21] with ([2; 5; 8; 9; 14; 17] ++ 19 :: [21]).
        apply Permutation_cons_app.
        simpl. apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; red; simpl; discriminate) ]).
        apply Sorted_nil.
Qed.