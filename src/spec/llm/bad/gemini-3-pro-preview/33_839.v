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

Ltac solve_perm :=
  simpl;
  match goal with
  | |- Permutation [] [] => apply Permutation_nil
  | |- Permutation (?x :: ?xs) ?ys =>
    let rec aux l1 l2 :=
      match l2 with
      | x :: ?l2' =>
        apply Permutation_trans with (x :: (l1 ++ l2'));
        [ apply Permutation_cons; solve_perm
        | apply Permutation_sym; apply Permutation_middle ]
      | ?y :: ?l2' =>
        aux (l1 ++ [y]) l2'
      end
    in aux (@nil Z) ys
  end.

Example test_case : sort_third_spec 
  [300; 500; 6; 7; 290; 8; 289; 20; -105; -277; 104; 10; 3; 4; 700; 900; -901; 800; 1000; -901; -277] 
  [-277; 500; 6; 3; 290; 8; 7; 20; -105; 289; 104; 10; 300; 4; 700; 900; -901; 800; 1000; -901; -277].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 22 (destruct i; [
        simpl in H; try contradiction;
        simpl; reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * solve_perm.
      * simpl.
        repeat (apply Sorted_cons; [ apply Z.leb_le; vm_compute; reflexivity | ]).
        apply Sorted_nil.
Qed.