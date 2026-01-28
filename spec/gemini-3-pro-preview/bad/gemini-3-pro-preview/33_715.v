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

Lemma perm_skip_middle : forall (A : Type) (x : A) (l l1 l2 : list A), 
  Permutation l (l1 ++ l2) -> Permutation (x :: l) (l1 ++ x :: l2).
Proof.
  intros. apply Permutation_trans with (x :: l1 ++ l2).
  - apply Permutation_cons. assumption.
  - apply Permutation_middle.
Qed.

Ltac solve_perm :=
  simpl;
  match goal with
  | |- Permutation [] [] => apply Permutation_nil
  | |- Permutation (?x :: ?xs) ?ys =>
      let rec split_list acc l :=
        match l with
        | x :: ?t =>
            apply (perm_skip_middle Z x xs acc t);
            solve_perm
        | ?y :: ?t =>
            split_list (acc ++ [y]) t
        end
      in split_list (@nil Z) ys
  end.

Ltac solve_sorted :=
  repeat (apply Sorted_cons; [
    simpl; try apply HdRel_nil; try apply HdRel_cons; simpl; try discriminate; try trivial
  | ]); apply Sorted_nil.

Example test_case : sort_third_spec 
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 8; 15; 7; 3; 12; 4; 5; 700; 900; 799; -200; -901; 800; 1000; 5; 8]
  [-901; 500; 6; 4; 8; 289; 5; -105; -277; 7; 8; 15; 7; 3; 12; 20; 5; 700; 104; 799; -200; 300; 800; 1000; 900; 8].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      repeat (destruct i as [|i]; [ simpl in *; try congruence; try reflexivity | ]).
      simpl. reflexivity.
    + split.
      * solve_perm.
      * simpl. solve_sorted.
Qed.