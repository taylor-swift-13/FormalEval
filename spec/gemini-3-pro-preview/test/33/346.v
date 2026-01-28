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
  [19; 0; -901; 2; 3; 4; 5; 6; 16; 7; 8; 9; 10; 11; 12; 14; 15; 16; 17; 18; 19; 21; 20; 4] 
  [2; 0; -901; 5; 3; 4; 7; 6; 16; 10; 8; 9; 14; 11; 12; 17; 15; 16; 19; 18; 19; 21; 20; 4].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We destruct i enough times to cover the list length (24) *)
      do 24 (destruct i; [ 
        simpl; try (exfalso; apply H; reflexivity); reflexivity 
      | ]).
      (* For i >= 24, both lists are empty *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [2; 5; 7; 10; 14; 17; 19; 21] [19; 2; 5; 7; 10; 14; 17; 21] *)
        (* We rearrange LHS to match RHS structure for Permutation_cons_app *)
        change [2; 5; 7; 10; 14; 17; 19; 21] with ([2; 5; 7; 10; 14; 17] ++ 19 :: [21]).
        apply Permutation_sym.
        apply Permutation_cons_app.
        simpl. apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; apply HdRel_cons; lia ]).
        apply Sorted_nil.
Qed.