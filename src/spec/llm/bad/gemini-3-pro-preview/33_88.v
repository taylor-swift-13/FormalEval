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

Example test_case : sort_third_spec [27; 1; 1; 1; 4; 27; 1] [1; 1; 1; 1; 4; 27; 27].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* Check indices 0 to 6 explicitly, then default for >= 7 *)
      do 7 (destruct i; [ simpl in H; try contradiction; simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        (* Goal: Permutation [1; 1; 27] [27; 1; 1] *)
        eapply perm_trans.
        apply perm_skip. apply perm_swap. (* [1; 27; 1] *)
        apply perm_swap. (* [27; 1; 1] *)
      * simpl.
        apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_cons.
              ** apply Sorted_nil.
              ** apply HdRel_nil.
           ++ apply HdRel_cons. simpl. lia.
        -- apply HdRel_cons. simpl. lia.
Qed.