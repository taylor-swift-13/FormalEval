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
  [1; 2; 3; -3; 5; 1; 16; -8; 8; -12; 7; 6; 1; 16] 
  [-12; 2; 3; -3; 5; 1; 1; -8; 8; 1; 7; 6; 16; 16].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We destruct i for all valid indices 0 to 13. For i >= 14 both are None. *)
      do 14 (destruct i; [ simpl in *; try contradiction; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-12; -3; 1; 1; 16] [1; -3; 16; -12; 1] *)
        (* We transform the LHS to match RHS step by step *)
        apply perm_trans with (l' := [1; -12; -3; 1; 16]).
        { (* Swap -12 and 1 (indices 0 and 2 in original) *)
          apply perm_trans with (l' := [-12; 1; -3; 1; 16]).
          - apply perm_skip. apply perm_swap.
          - apply perm_swap.
        }
        apply perm_skip. (* Match 1 *)
        apply perm_trans with (l' := [-3; -12; 1; 16]).
        { (* Swap -12 and -3 *)
          apply perm_swap.
        }
        apply perm_skip. (* Match -3 *)
        apply perm_trans with (l' := [16; -12; 1]).
        { (* Swap -12 and 16, then 1 and 16 to get 16 to front *)
          apply perm_trans with (l' := [-12; 16; 1]).
          - apply perm_skip. apply perm_swap.
          - apply perm_swap.
        }
        apply perm_skip. (* Match 16 *)
        apply perm_skip. (* Match -12 *)
        apply Permutation_refl. (* Match 1 *)
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- apply HdRel_cons. compute. trivial.
        -- apply HdRel_cons. compute. trivial.
        -- apply HdRel_cons. compute. trivial.
        -- apply HdRel_cons. compute. trivial.
Qed.