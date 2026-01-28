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
  [2; 3; -3; 5; 1; 16; 16; -8; 9; -12; 7; -12; -9; 16] 
  [-12; 3; -3; -9; 1; 16; 2; -8; 9; 5; 7; -12; 16; 16].
Proof.
  unfold sort_third_spec.
  split.
  - (* length res = length l *)
    simpl. reflexivity.
  - split.
    + (* Preservation of indices not divisible by 3 *)
      intros i H.
      (* Verify for indices 0 to 13. For i >= 14, both lists return None. *)
      do 14 (destruct i; [
        simpl in *; 
        try (exfalso; apply H; reflexivity); 
        try reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-12; -9; 2; 5; 16] [2; 5; 16; -12; -9] *)
        apply Permutation_trans with (l' := -12 :: [2; 5; 16; -9]).
        -- apply perm_skip.
           change [2; 5; 16; -9] with ([2; 5; 16] ++ -9 :: []).
           apply Permutation_middle.
        -- change [2; 5; 16; -12; -9] with ([2; 5; 16] ++ -12 :: [-9]).
           apply Permutation_middle.
      * (* Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons || apply Sorted_nil || apply HdRel_cons || apply HdRel_nil).
        all: try (apply Z.leb_le; reflexivity).
Qed.