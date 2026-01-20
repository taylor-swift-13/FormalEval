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
  [0; 8; 9; -1; 6; -4; -5; 12; 0; 8; 0] 
  [-5; 8; 9; -1; 6; -4; 0; 12; 0; 8; 0].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We check indices up to the length of the list (11 elements) *)
      do 11 (destruct i; [ simpl in *; try reflexivity; try (intros C; discriminate) | ]).
      (* For i >= 11, both are None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-5; -1; 0; 8] [0; -1; -5; 8] *)
        apply perm_trans with (l' := [-1; -5; 0; 8]).
        { apply perm_swap. }
        apply perm_trans with (l' := [-1; 0; -5; 8]).
        { apply perm_skip. apply perm_swap. }
        apply perm_swap.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* Goal: Sorted Z.le [-5; -1; 0; 8] *)
        repeat (constructor; try lia).
Qed.