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
  [1; 2; 3; -3; 5; 1; 16; -8; 9; -12; 7; 6; 16; 3] 
  [-12; 2; 3; -3; 5; 1; 1; -8; 9; 16; 7; 6; 16; 3].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* Check indices 0 to 13 one by one *)
      do 14 (destruct i; [ simpl in *; try congruence; try reflexivity | ]).
      (* For i >= 14, both lists return None *)
      simpl. reflexivity.
    + split.
      * simpl.
        (* Goal: Permutation [-12; -3; 1; 16; 16] [1; -3; 16; -12; 16] *)
        (* Bring -12 to the front of the right-hand list using transitivity and swaps *)
        apply Permutation_trans with (l' := [1; -3; -12; 16; 16]).
        { repeat apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := [1; -12; -3; 16; 16]).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := [-12; 1; -3; 16; 16]).
        { apply perm_swap. }
        (* Now heads match (-12), check tails *)
        apply perm_skip.
        (* Goal: Permutation [-3; 1; 16; 16] [1; -3; 16; 16] *)
        apply perm_swap.
      * simpl.
        (* Verify sortedness of [-12; -3; 1; 16; 16] *)
        repeat (apply Sorted_cons; [ simpl; try lia | ]).
        apply Sorted_nil.
Qed.