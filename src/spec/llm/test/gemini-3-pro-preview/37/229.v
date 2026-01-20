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

Ltac find_and_split x pre post :=
  match post with
  | x :: ?post' =>
      apply Permutation_trans with (l' := x :: (pre ++ post'));
      [ apply perm_skip | apply Permutation_middle ]
  | ?y :: ?post' => find_and_split x (pre ++ [y]) post'
  end.

Ltac solve_perm :=
  simpl;
  match goal with
  | |- Permutation [] [] => apply perm_nil
  | |- Permutation (?x :: ?l) (?x :: ?r) => apply perm_skip; solve_perm
  | |- Permutation (?x :: ?l) ?r =>
      find_and_split x (@nil Z) r; solve_perm
  end.

Example test_sort_even_case : sort_even_spec 
  [5; -2; -12; 4; 23; 2; 3; -13; 11; 12; -10; 3; 2; 4; -10] 
  [-12; -2; -10; 4; -10; 2; 2; -13; 3; 12; 5; 3; 11; 4; 23].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 15 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl. solve_perm.
      * simpl. repeat (constructor; try lia).
Qed.