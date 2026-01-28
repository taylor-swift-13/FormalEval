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
  [-7; 6; 7; 290; 8; 289; 20; 104; -277; 200; 3; 4; -8; 700; -2; -901; 800; 1000] 
  [-901; 6; 7; -8; 8; 289; -7; 104; -277; 20; 3; 4; 200; 700; -2; 290; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check the first 18 indices explicitly *)
      do 18 (destruct i; [ simpl in *; try (contradiction || reflexivity) | ]).
      (* For i >= 18, both lists are exhausted *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-901; -8; -7; 20; 200; 290] [-7; 290; 20; 200; -8; -901] *)
        apply (Permutation_cons_app _ [-7; 290; 20; 200; -8] []). simpl.
        apply (Permutation_cons_app _ [-7; 290; 20; 200] []). simpl.
        apply (Permutation_cons_app _ [] [290; 20; 200]). simpl.
        apply (Permutation_cons_app _ [290] [200]). simpl.
        apply (Permutation_cons_app _ [290] []). simpl.
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat constructor; try lia.
Qed.