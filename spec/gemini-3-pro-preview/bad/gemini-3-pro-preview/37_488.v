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

Ltac bubble :=
  match goal with
  | |- Permutation (?x :: ?tl) (?x :: ?rest) =>
      apply Permutation_refl
  | |- Permutation (?y :: ?tl) (?x :: ?rest) =>
      eapply Permutation_trans; [
        apply Permutation_cons; bubble |
        apply Permutation_swap
      ]
  end.

Ltac solve_perm :=
  match goal with
  | |- Permutation [] [] => apply Permutation_refl
  | |- Permutation (?x :: ?xs) ?ys =>
      eapply Permutation_trans; [
        | apply Permutation_sym; bubble
      ];
      apply Permutation_cons; solve_perm
  end.

Example test_sort_even_case : sort_even_spec [-5; -7; 2; -5; 2; 9; -4; -3; 2; 8; 7; 3; 7; 3; -7; 2; -4] [-7; -7; -5; -5; -4; 9; -4; -3; 2; 8; 2; 3; 2; 3; 7; 2; 7].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 17 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl. solve_perm.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_cons; try lia; try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.