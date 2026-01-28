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

Ltac find_elem x lst :=
  match lst with
  | x :: ?tl => constr:((@nil Z, tl))
  | ?y :: ?tl =>
      let res := find_elem x tl in
      match res with
      | (?l1, ?l2) => constr:((y :: l1, l2))
      end
  end.

Ltac solve_perm :=
  simpl;
  match goal with
  | [ |- Permutation [] [] ] => apply Permutation_nil
  | [ |- Permutation (?x :: ?xs) ?ys ] =>
      let res := find_elem x ys in
      match res with
      | (?l1, ?l2) =>
          apply Permutation_trans with (l' := x :: (l1 ++ l2));
          [ apply perm_skip; solve_perm 
          | apply Permutation_sym; apply (Permutation_middle Z l1 l2 x) ]
      end
  end.

Example test_sort_even_case : sort_even_spec 
  [5; 3; -5; 0; 2; -3; -10; 0; 123; 1; 0; -10; 123; 5] 
  [-10; 3; -5; 0; 0; -3; 2; 0; 5; 1; 123; -10; 123; 5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      repeat (destruct i as [|i]; [
        simpl in Hodd; try discriminate; simpl; reflexivity 
      | ]).
      simpl in Hlen; lia.
    + split.
      * solve_perm.
      * simpl.
        repeat (apply Sorted_cons; [ | try (apply HdRel_cons; lia); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.