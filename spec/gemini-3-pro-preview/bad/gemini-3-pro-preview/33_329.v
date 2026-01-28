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
  [1; 2; 3; -7; 105; 1; 0; -8; 9; -12; 7; 6; 6; 1] 
  [-12; 2; 3; -7; 105; 1; 0; -8; 9; 1; 7; 6; 6; 1].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      do 15 (destruct i; [
        simpl in *; 
        try (exfalso; apply H; reflexivity); 
        try reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        (* Goal: Permutation [-12; -7; 0; 1; 6] [1; -7; 0; -12; 6] *)
        simpl.
        apply Permutation_cons_app with (l1 := [1; -7; 0]) (l2 := [6]). simpl.
        apply Permutation_cons_app with (l1 := [1]) (l2 := [0; 6]). simpl.
        apply Permutation_cons_app with (l1 := [1]) (l2 := [6]). simpl.
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [| compute; discriminate]).
        apply Sorted_nil.
Qed.