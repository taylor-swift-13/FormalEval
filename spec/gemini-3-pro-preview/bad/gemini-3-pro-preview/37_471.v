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

Ltac find_split x l k :=
  match l with
  | x :: ?t => k (@nil Z) t
  | ?h :: ?t =>
      find_split x t ltac:(fun l1 l2 => k (h :: l1) l2)
  end.

Ltac solve_perm :=
  match goal with
  | |- Permutation [] [] => apply Permutation_nil
  | |- Permutation (?x :: ?xs) ?y =>
      find_split x y ltac:(fun l1 l2 =>
        apply Permutation_trans with (l' := l1 ++ x :: l2);
        [ | reflexivity ];
        apply Permutation_sym;
        apply Permutation_middle;
        apply Permutation_sym;
        simpl;
        solve_perm
      )
  end.

Example test_sort_even_case : sort_even_spec 
  [5; 2; -13; 3; -5; 2; -10; -3; -2; 3; -8; 0; -5; 1; -10; -9; 3; -2] 
  [-13; 2; -10; 3; -10; 2; -8; -3; -5; 3; -5; 0; -2; 1; 3; -9; 5; -2].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 19 (destruct i; [ try (simpl in Hodd; discriminate); try (simpl; reflexivity) | ]).
      simpl in Hlen. lia.
    + split.
      * simpl. solve_perm.
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.