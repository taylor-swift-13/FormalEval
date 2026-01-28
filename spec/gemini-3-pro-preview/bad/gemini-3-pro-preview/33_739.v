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

Ltac find_split x l :=
  match l with
  | x :: ?rest => constr:((@nil Z, rest))
  | ?y :: ?rest =>
      let res := find_split x rest in
      match res with
      | (?pre, ?post) => constr:((y :: pre, post))
      end
  end.

Ltac solve_perm :=
  simpl;
  match goal with
  | |- Permutation [] [] => apply Permutation_nil
  | |- Permutation (?x :: ?xs) ?ys =>
      let pair := find_split x ys in
      match pair with
      | (?pre, ?post) =>
          apply (Permutation_trans (l' := x :: (pre ++ post)));
          [ apply Permutation_cons; solve_perm 
          | apply Permutation_sym; 
            replace ys with (pre ++ x :: post) by (simpl; reflexivity);
            apply Permutation_cons_app ]
      end
  end.

Example test_case : sort_third_spec 
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 8; 7; 3; 12; 4; 5; 700; 900; 799; 6; -200; -901; 800; 1000; 5; 8]
  [-901; 500; 6; 3; 8; 289; 5; -105; -277; 5; 8; 7; 7; 12; 4; 20; 700; 900; 104; 6; -200; 300; 800; 1000; 799; 8].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 26 (destruct i; [ try (exfalso; apply H; reflexivity); try reflexivity | ]).
      simpl. reflexivity.
    + split.
      * solve_perm.
      * simpl.
        repeat (apply Sorted_cons; [ simpl; try apply HdRel_nil; try (apply HdRel_cons; simpl; trivial) | ]).
        apply Sorted_nil.
Qed.