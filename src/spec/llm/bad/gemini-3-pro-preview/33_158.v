Existing Coq output file content 
specification for the first test case `input = [[19%Z; 0%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 20%Z; 11%Z]], output = [3%Z; 0%Z; 2%Z; 6%Z; 4%Z; 5%Z; 9%Z; 7%Z; 8%Z; 11%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 20%Z; 19%Z]`:
```coq
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
  [19; 0; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 11]
  [3; 0; 2; 6; 4; 5; 9; 7; 8; 11; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 19].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices preservation *)
      intros i H.
      (* Check for each index in the concrete list *)
      do 22 (destruct i; [ simpl in H; try discriminate; simpl; reflexivity | ]).
      (* For indices beyond the list length *)
      simpl. reflexivity.
    + split.
      * (* Permutation of thirds *)
        simpl.
        (* Goal: Permutation [3; 6; 9; 11; 12; 15; 18; 19] [19; 3; 6; 9; 12; 15; 18; 11] *)
        (* Prove by explicit swaps *)
        etransitivity. 2: apply perm_swap. apply perm_skip. (* Move 3 *)
        etransitivity. 2: apply perm_swap. apply perm_skip. (* Move 6 *)
        etransitivity. 2: apply perm_swap. apply perm_skip. (* Move 9 *)
        (* Move 11 from end to position *)
        etransitivity. 2: (do 3 apply perm_skip; apply perm_swap).
        etransitivity. 2: (do 2 apply perm_skip; apply perm_swap).
        etransitivity. 2: (do 1 apply perm_skip; apply perm_swap).
        etransitivity. 2: apply perm_swap.
        apply perm_skip.
        (* Move 12, 15, 18 *)
        etransitivity. 2: apply perm_swap. apply perm_skip.
        etransitivity. 2: apply perm_swap. apply perm_skip.
        etransitivity. 2: apply perm_swap. apply perm_skip.
        apply Permutation_refl.
      * (* Sortedness *)
        simpl.
        repeat (apply Sorted_cons; [ constructor; compute; auto | ]).
        apply Sorted_nil.
Qed.