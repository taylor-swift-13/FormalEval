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

Example test_case : sort_third_spec [-4; 7; 3; -6; 1000; 0; -8; 6; 290; 2; 289; 1; 1000] [-8; 7; 3; -6; 1000; 0; -4; 6; 290; 2; 289; 1; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      do 13 (destruct i; [ simpl in *; try (exfalso; apply H; reflexivity); try reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        change [-8; -6; -4; 2; 1000] with ([-8; -6; -4] ++ [2; 1000]).
        change [-4; -6; -8; 2; 1000] with ([-4; -6; -8] ++ [2; 1000]).
        apply Permutation_app_tail.
        replace [-4; -6; -8] with (rev [-8; -6; -4]) by reflexivity.
        apply Permutation_rev.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (first [ apply Sorted_cons; [ | simpl; first [ apply HdRel_nil | apply HdRel_cons; compute; discriminate ] ] | apply Sorted_nil ]).
Qed.