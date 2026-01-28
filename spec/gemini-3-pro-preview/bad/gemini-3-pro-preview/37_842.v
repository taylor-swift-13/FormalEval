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

Lemma perm_move : forall (A : Type) (a : A) (l l1 l2 : list A),
  Permutation l (l1 ++ l2) -> Permutation (a :: l) (l1 ++ a :: l2).
Proof.
  intros.
  apply Permutation_trans with (a :: l1 ++ l2).
  - apply Permutation_cons; assumption.
  - apply Permutation_sym. apply Permutation_middle.
Qed.

Example test_sort_even_case : sort_even_spec 
  [-5; -7; 2; 10; 0; 9; 5; -3; 2; 8; 10; 3; 7; 2; -3; -5]
  [-5; -7; -3; 10; 0; 9; 2; -3; 2; 8; 5; 3; 7; 2; 10; -5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 16 (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_cons.
        apply perm_move with (l1 := [-3; 0]) (l2 := [2; 5; 7; 10]). simpl.
        apply perm_move with (l1 := [-3]) (l2 := [2; 5; 7; 10]). simpl.
        apply perm_move with (l1 := [-3; 2]) (l2 := [7; 10]). simpl.
        apply perm_move with (l1 := [-3]) (l2 := [7; 10]). simpl.
        apply perm_move with (l1 := [-3; 7]) (l2 := []). simpl.
        apply perm_move with (l1 := [-3]) (l2 := []). simpl.
        apply Permutation_cons.
        apply Permutation_nil.
      * simpl.
        repeat apply Sorted_cons.
        all: try apply Sorted_nil.
        all: try apply HdRel_nil.
        all: apply HdRel_cons; lia.
Qed.