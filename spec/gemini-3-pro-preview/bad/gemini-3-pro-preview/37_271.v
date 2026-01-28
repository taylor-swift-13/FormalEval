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

Ltac split_at_elem x l :=
  match l with
  | x :: ?tl => constr:((@nil Z, tl))
  | ?y :: ?tl =>
      let res := split_at_elem x tl in
      match res with
      | (?l1, ?l2) => constr:((y :: l1, l2))
      end
  end.

Ltac solve_perm_once :=
  match goal with
  | |- Permutation (?x :: ?tl) ?r =>
      let s := split_at_elem x r in
      match s with
      | (?l1, ?l2) =>
          apply Permutation_trans with (l' := x :: (l1 ++ l2));
          [ apply perm_skip | 
            apply Permutation_sym; 
            apply Permutation_cons_app; 
            apply Permutation_refl ]
      end
  end.

Example test_sort_even_case : sort_even_spec 
  [4; 2; 2; 0; 9; 5; -3; 2; 8; 3; 7; 2; 2; 8; 2] 
  [-3; 2; 2; 0; 2; 5; 2; 2; 4; 3; 7; 2; 8; 8; 9].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 15 (destruct i as [|i]; [
        simpl in Hodd; try discriminate; simpl; reflexivity
      | ]).
      simpl in Hlen; lia.
    + split.
      * simpl.
        repeat solve_perm_once.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | first [ apply HdRel_nil | apply HdRel_cons; lia ] ]).
        apply Sorted_nil.
Qed.