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

Lemma perm_move : forall (A : Type) (x : A) (l1 l2 : list A),
  Permutation (x :: l1 ++ l2) (l1 ++ x :: l2).
Proof.
  intros. induction l1.
  - simpl. apply Permutation_refl.
  - simpl. apply Permutation_trans with (a :: x :: l1 ++ l2).
    + constructor.
    + constructor. apply IHl1.
Qed.

Example test_sort_even_case : sort_even_spec 
  [2; 2; 3; 4; 6; 7; 7; 8; 2; 2; 7; 6; 2] 
  [2; 2; 2; 4; 2; 7; 3; 8; 6; 2; 7; 6; 7].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      repeat (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_cons.
        apply Permutation_trans with (2 :: [3; 6; 7] ++ [7; 2]).
        { apply Permutation_sym. apply perm_move. }
        apply Permutation_cons.
        apply Permutation_trans with (2 :: [3; 6; 7; 7] ++ []).
        { apply Permutation_sym. apply perm_move. }
        apply Permutation_cons.
        simpl. rewrite app_nil_r. apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_cons; try apply HdRel_nil; lia ]).
        apply Sorted_nil.
Qed.