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
  lazymatch goal with
  | |- Permutation [] [] => apply Permutation_refl
  | |- Permutation (?x :: ?xs) ?ys =>
     let rec split_list l acc :=
       match l with
       | ?h :: ?tl =>
         tryif unify h x then
           constr:((acc, tl))
         else
           split_list tl (acc ++ [h])
       end
     in
     let p := split_list ys (@nil Z) in
     match p with
     | (?l1, ?l2) =>
       apply Permutation_trans with (l' := x :: (l1 ++ l2));
       [ apply Permutation_cons; solve_perm
       | apply Permutation_middle ]
     end
  end.

Example test_sort_even_case : sort_even_spec [1; 3; 4; 6; 7; 8; -9; -4; -4; 2] [-9; 3; -4; 6; 1; 8; 4; -4; 7; 2].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 10 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl. solve_perm.
      * simpl.
        repeat (apply Sorted_cons; [ | try (apply HdRel_cons; lia); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.