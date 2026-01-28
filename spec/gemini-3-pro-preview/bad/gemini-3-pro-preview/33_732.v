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
  [10; 9; 8; 7; 7; 5; 4; 3; 2; 1; -1; -2; -3; -4; -5; -6; -7; -8; -9; -10] 
  [-9; 9; 8; -6; 7; 5; -3; 3; 2; 1; -1; -2; 4; -4; -5; 7; -7; -8; 10; -10].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* Handle each index case individually. The list has 20 elements. *)
      do 20 (destruct i; [ simpl in *; try contradiction; reflexivity | ]).
      (* For i >= 20, both nth_error return None *)
      simpl. reflexivity.
    + split.
      * simpl.
        (* Proving Permutation: The result extracted list is exactly the reverse of the input extracted list *)
        replace [-9; -6; -3; 1; 4; 7; 10] with (rev [10; 7; 4; 1; -3; -6; -9]) by reflexivity.
        apply Permutation_rev.
      * simpl.
        (* Proving Sortedness: Construct the sorted list proof element by element *)
        repeat (apply Sorted_cons; [ simpl; hnf; try congruence | ]).
        apply Sorted_nil.
Qed.