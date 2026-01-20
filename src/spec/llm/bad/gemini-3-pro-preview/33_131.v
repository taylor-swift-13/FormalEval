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
  [1; 2; 3; 5; 1; 0; -8; 9; -12; 7; 6; 6; 1; 6] 
  [-8; 2; 3; 1; 1; 0; 1; 9; -12; 5; 6; 6; 7; 6].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check equality for each index up to list length *)
      do 15 (destruct i; [ simpl; try reflexivity; try (exfalso; apply H; compute; discriminate) | ]).
      (* For indices beyond list length, both are None *)
      reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        (* Target: [-8; 1; 1; 5; 7] vs Source: [1; 5; -8; 7; 1] *)
        simpl.
        (* Match -8 *)
        apply Permutation_cons_app with (l1 := [1; 5]) (l2 := [7; 1]).
        simpl.
        (* Match 1 *)
        apply Permutation_cons_app with (l1 := []) (l2 := [5; 7; 1]).
        simpl.
        (* Match 1 *)
        apply Permutation_cons_app with (l1 := [5; 7]) (l2 := []).
        simpl.
        (* Remaining [5; 7] matches [5; 7] *)
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_cons.
              ** apply Sorted_cons.
                 --- apply Sorted_cons.
                     +++ apply Sorted_nil.
                     +++ apply HdRel_nil.
                 --- apply HdRel_cons. apply Z.leb_le. reflexivity.
              ** apply HdRel_cons. apply Z.leb_le. reflexivity.
           ++ apply HdRel_cons. apply Z.leb_le. reflexivity.
        -- apply HdRel_cons. apply Z.leb_le. reflexivity.
Qed.