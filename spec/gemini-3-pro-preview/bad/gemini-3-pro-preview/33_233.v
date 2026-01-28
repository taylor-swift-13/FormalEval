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
  [2; 3; -3; 5; 1; 16; 16; -8; 9; -12; 7; 6; -12; 16; 7] 
  [-12; 3; -3; -12; 1; 16; 2; -8; 9; 5; 7; 6; 16; 16; 7].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We destruct i enough times to cover the list length (15) *)
      do 16 (destruct i as [|i]; [ simpl in *; try contradiction; reflexivity | ]).
      (* For i >= 16, both lists are exhausted *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Target: Permutation [-12; -12; 2; 5; 16] [2; 5; 16; -12; -12] *)
        apply Permutation_trans with (l' := -12 :: [2; 5; 16; -12]).
        { apply perm_skip.
          apply Permutation_cons_app with (l1:=[2; 5; 16]) (l2:=[]).
          simpl. rewrite app_nil_r. apply Permutation_refl. }
        { apply Permutation_cons_app with (l1:=[2; 5; 16]) (l2:=[-12]).
          simpl. apply Permutation_refl. }
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_cons; try apply HdRel_nil; try (simpl; auto with zarith) ]).
        apply Sorted_nil.
Qed.