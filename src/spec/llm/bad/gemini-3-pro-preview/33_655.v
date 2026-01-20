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

Example test_case : sort_third_spec [1; 2; 3; -3; 5; 1; -8; 9; -12; 7] [-8; 2; 3; -3; 5; 1; 1; 9; -12; 7].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* We check the condition for the first 10 indices and the tail *)
      do 10 (destruct i; [ simpl in *; try contradiction; reflexivity | ]).
      (* For i >= 10, both lists return None *)
      simpl. reflexivity.
    + split.
      * (* Permutation check *)
        simpl.
        (* Target: Permutation [-8; -3; 1; 7] [1; -3; -8; 7] *)
        apply Permutation_Add. apply Add_cons. apply Add_cons. apply Add_head.
        (* Target: Permutation [-3; 1; 7] [1; -3; 7] *)
        apply Permutation_Add. apply Add_cons. apply Add_head.
        (* Target: Permutation [1; 7] [1; 7] *)
        apply Permutation_refl.
      * (* Sorted check *)
        simpl.
        apply Sorted_cons. apply HdRel_cons. lia.
        apply Sorted_cons. apply HdRel_cons. lia.
        apply Sorted_cons. apply HdRel_cons. lia.
        apply Sorted_cons. apply HdRel_nil.
        apply Sorted_nil.
Qed.