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
  [19; 0; -901; 2; 14; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 17; 19; 21; 20; 200; 2]
  [2; 0; -901; 4; 14; 3; 7; 5; 6; 10; 8; 9; 13; 11; 12; 16; 14; 15; 19; 17; 17; 19; 21; 20; 200; 2].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We destruct i for all indices up to the length of the list (26) *)
      do 26 (destruct i; [
        simpl; 
        try (match goal with | |- _ = _ => reflexivity end);
        try (intro Hc; compute in Hc; congruence)
      | ]).
      (* For indices >= 26, both nth_error return None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        (* Compute the extracted lists to concrete lists *)
        vm_compute.
        (* We bubble the element 19 down to its sorted position *)
        apply perm_trans with (l' := [2; 19; 4; 7; 10; 13; 16; 19; 200]); [ apply perm_skip | apply perm_swap ].
        apply perm_trans with (l' := [4; 19; 7; 10; 13; 16; 19; 200]); [ apply perm_skip | apply perm_swap ].
        apply perm_trans with (l' := [7; 19; 10; 13; 16; 19; 200]); [ apply perm_skip | apply perm_swap ].
        apply perm_trans with (l' := [10; 19; 13; 16; 19; 200]); [ apply perm_skip | apply perm_swap ].
        apply perm_trans with (l' := [13; 19; 16; 19; 200]); [ apply perm_skip | apply perm_swap ].
        apply perm_trans with (l' := [16; 19; 19; 200]); [ apply perm_skip | apply perm_swap ].
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        vm_compute.
        repeat (apply Sorted_cons; [ simpl; auto with zarith | ]).
        apply Sorted_nil.
Qed.