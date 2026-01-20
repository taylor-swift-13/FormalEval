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
  [5; 2; 9; 3; -7; 8; 8; 0; 1; 13; 6; -2; 19] 
  [3; 2; 9; 5; -7; 8; 8; 0; 1; 13; 6; -2; 19].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices not mod 3 *)
      intros i H.
      (* Check indices 0 to 12 explicitly *)
      do 13 (destruct i; [ simpl in H; try discriminate; simpl; reflexivity | ]).
      (* For indices >= 13, both lists are empty *)
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        (* The extracted lists are [3; 5; 8; 13; 19] and [5; 3; 8; 13; 19] *)
        apply Permutation_swap.
      * (* Sorted *)
        simpl.
        (* Check sortedness of [3; 5; 8; 13; 19] *)
        apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_cons.
              ** apply Sorted_cons.
                 --- apply Sorted_cons.
                     +++ apply Sorted_nil.
                     +++ apply HdRel_nil.
                 --- constructor. simpl. discriminate.
              ** constructor. simpl. discriminate.
           ++ constructor. simpl. discriminate.
        -- constructor. simpl. discriminate.
Qed.