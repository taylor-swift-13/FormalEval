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
  [9; -1; 7; 700; -1; 6; -4; 3; 11; 3; -1] 
  [-4; -1; 7; 3; -1; 6; 9; 3; 11; 700; -1].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 11 (destruct i; [
        try (exfalso; apply H; reflexivity);
        try reflexivity
        | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        change (Permutation ([-4; 3] ++ [9; 700]) ([9; 700] ++ [-4; 3])).
        apply Permutation_app_comm.
      * simpl.
        apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_cons.
              ** apply Sorted_cons.
                 --- apply Sorted_nil.
                 --- apply HdRel_nil.
              ** apply HdRel_cons. apply Z.leb_le. reflexivity.
           ++ apply HdRel_cons. apply Z.leb_le. reflexivity.
        -- apply HdRel_cons. apply Z.leb_le. reflexivity.
Qed.