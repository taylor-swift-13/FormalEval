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
  [1; 15; 2; 3; 4; 5; 6; 7; 8; 10; 11; 1000; 12; 13; 14; 15; 16; 17; 18; 20; 20; 7; 8] 
  [1; 15; 2; 3; 4; 5; 6; 7; 8; 7; 11; 1000; 10; 13; 14; 12; 16; 17; 15; 20; 20; 18; 8].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We check each index. Since the list is finite (length 23), we can destruct i 23 times. *)
      do 23 (destruct i; [ simpl in *; try congruence; reflexivity | ]).
      (* For i >= 23, both nth_error return None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        vm_compute.
        (* Goal: Permutation [1; 3; 6; 7; 10; 12; 15; 18] [1; 3; 6; 10; 12; 15; 18; 7] *)
        apply perm_skip. (* 1 *)
        apply perm_skip. (* 3 *)
        apply perm_skip. (* 6 *)
        (* Goal: Permutation [7; 10; 12; 15; 18] [10; 12; 15; 18; 7] *)
        (* Move 7 to the end *)
        apply perm_swap. (* [10; 7; ...] *)
        apply perm_skip. (* 10 *)
        apply perm_swap. (* [12; 7; ...] *)
        apply perm_skip. (* 12 *)
        apply perm_swap. (* [15; 7; ...] *)
        apply perm_skip. (* 15 *)
        apply perm_swap. (* [18; 7; ...] *)
        apply perm_skip. (* 18 *)
        apply perm_skip. (* 7 *)
        apply perm_nil.
      * (* 4. Sortedness of extracted thirds *)
        vm_compute.
        (* Goal: Sorted Z.le [1; 3; 6; 7; 10; 12; 15; 18] *)
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; vm_compute; exact I) ]).
        apply Sorted_nil.
Qed.