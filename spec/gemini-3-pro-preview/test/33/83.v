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
  [11; 22; 100; 33; 44; 55; 66; 77; 88; 88; 32; 99; 77; 77; 11] 
  [11; 22; 100; 33; 44; 55; 66; 77; 88; 77; 32; 99; 88; 77; 11].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 15 (destruct i; [ simpl in *; try solve [contradict H; reflexivity]; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        repeat apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- simpl. apply HdRel_cons. lia.
        -- simpl. apply HdRel_cons. lia.
        -- simpl. apply HdRel_cons. lia.
        -- simpl. apply HdRel_cons. lia.
Qed.