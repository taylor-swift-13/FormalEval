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

Ltac solve_perm :=
  simpl;
  repeat match goal with
  | |- Permutation [] [] => apply Permutation_refl
  | |- Permutation (?x :: ?tl) (?x :: ?tr) => apply Permutation_cons
  | |- Permutation (?x :: ?tl) ?r =>
      let rec search pre post :=
        match post with
        | x :: ?tail =>
          let r_equiv := constr:(pre ++ x :: tail) in
          transitivity (x :: pre ++ tail);
          [ apply Permutation_cons |
            change r with r_equiv;
            apply Permutation_sym; apply Permutation_middle ]
        | ?h :: ?tail =>
          let new_pre := constr:(pre ++ [h]) in
          search new_pre tail
        end
      in search (@nil Z) r
  end.

Example test_sort_even_case : sort_even_spec 
  [-5; -7; 123; 2; 10; 0; 9; 5; -3; 2; 8; 3; 7; 2; 8] 
  [-5; -7; -3; 2; 7; 0; 8; 5; 8; 2; 9; 3; 10; 2; 123].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 15 (destruct i; [ simpl in Hodd; try discriminate; simpl; try reflexivity | ]).
      simpl in Hlen; lia.
    + split.
      * unfold get_evens. solve_perm.
      * simpl. repeat (apply Sorted_cons; [ | first [ apply HdRel_nil | apply HdRel_cons; lia ] ]). apply Sorted_nil.
Qed.