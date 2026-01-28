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
  [-4; 3; 289; 290; 3; 0; -8; 899; 2; 0; 8; 7] 
  [-8; 3; 289; -4; 3; 0; 0; 899; 2; 290; 8; 7].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We destruct i for all valid indices to allow computation of mod and nth_error *)
      do 12 (destruct i; [
        (* For each index, check if i mod 3 = 0. *)
        (* If so, H implies False, solved by congruence. *)
        (* If not, simpl reduces nth_error to values, solved by reflexivity. *)
        try (compute in H; congruence); 
        simpl; reflexivity 
      | ]).
      (* For i >= 12, both nth_error are None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-8; -4; 0; 290] [-4; 290; -8; 0] *)
        apply perm_trans with (l' := [-8; -4; 290; 0]).
        { apply perm_skip. apply perm_skip. apply perm_swap. }
        apply perm_trans with (l' := [-4; -8; 290; 0]).
        { apply perm_swap. }
        { apply perm_skip. apply perm_swap. }
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        apply Sorted_cons.
        { apply Sorted_cons.
          { apply Sorted_cons.
            { apply Sorted_cons.
              { apply Sorted_nil. }
              { apply HdRel_nil. } }
            { apply HdRel_cons. simpl. trivial. } }
          { apply HdRel_cons. simpl. trivial. } }
        { apply HdRel_cons. simpl. trivial. }
Qed.