Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Fixpoint get_evens (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: [] => [x]
  | x :: _ :: tl => x :: get_evens tl
  end.

Definition sort_even_spec (l res : list Z) : Prop :=
  length l = length res /\
  (forall i : nat, (i < length l)%nat -> Nat.odd i = true -> nth i l 0 = nth i res 0) /\
  Permutation (get_evens l) (get_evens res) /\
  Sorted Z.le (get_evens res).

Ltac find_and_remove x l :=
  match l with
  | x :: ?tl => constr:((@nil Z, tl))
  | ?y :: ?tl =>
      let res := find_and_remove x tl in
      match res with
      | (?l1, ?l2) => constr:((y :: l1, l2))
      end
  end.

Ltac solve_perm :=
  match goal with
  | |- Permutation [] [] => apply Permutation_nil
  | |- Permutation (?x :: ?tl) ?rhs =>
      let pair := find_and_remove x rhs in
      match pair with
      | (?l1, ?l2) =>
          apply Permutation_trans with (l' := x :: (l1 ++ l2));
          [ apply Permutation_cons; simpl; solve_perm
          | apply Permutation_sym; apply Permutation_cons_app; reflexivity ]
      end
  end.

Example test_sort_even_case : sort_even_spec 
  [5; 3; 10; -5; 2; -12; -3; 3; -9; 1; 123; -1; 1; -10; 10; -5]
  [-9; 3; -3; -5; 1; -12; 2; 3; 5; 1; 10; -1; 10; -10; 123; -5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 16 (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl. solve_perm.
      * simpl. repeat (apply Sorted_cons; [ apply HdRel_cons; lia | ]). apply Sorted_nil.
Qed.