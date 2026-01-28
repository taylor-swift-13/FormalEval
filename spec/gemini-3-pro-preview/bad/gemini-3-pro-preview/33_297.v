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
  [16; 7; 3; -6; 3; 0; -8; 6; 2; 1; 8; 14] 
  [-8; 7; 3; -6; 3; 0; 1; 6; 2; 16; 8; 14].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Destruct i to handle finite indices and filter out i mod 3 = 0 cases *)
      do 13 (destruct i; [ simpl in *; try congruence; try reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-8; -6; 1; 16] [16; -6; -8; 1] *)
        (* Use symmetry to transform input [16; -6; -8; 1] into sorted output [-8; -6; 1; 16] *)
        apply Permutation_sym.
        (* 1. Swap 16 and -6: [-6; 16; -8; 1] *)
        eapply Permutation_trans. apply Permutation_swap.
        (* 2. Swap 16 and -8: [-6; -8; 16; 1] *)
        eapply Permutation_trans. apply Permutation_skip. apply Permutation_swap.
        (* 3. Swap 16 and 1: [-6; -8; 1; 16] *)
        eapply Permutation_trans. do 2 apply Permutation_skip. apply Permutation_swap.
        (* 4. Swap -6 and -8: [-8; -6; 1; 16] *)
        apply Permutation_swap.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        apply Sorted_cons.
        -- apply HdRel_cons. unfold Z.le. simpl. discriminate.
        -- apply Sorted_cons.
           ++ apply HdRel_cons. unfold Z.le. simpl. discriminate.
           ++ apply Sorted_cons.
              ** apply HdRel_cons. unfold Z.le. simpl. discriminate.
              ** apply Sorted_cons.
                 --- apply HdRel_nil.
                 --- apply Sorted_nil.
Qed.