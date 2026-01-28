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

Example test_sort_even_case : sort_even_spec [5; 10; -6; 2; -3; 3; -9; 0; 1; -10; 10; 10] [-9; 10; -6; 2; -3; 3; 1; 0; 5; -10; 10; 10].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 12 (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        change [-9; -6; -3; 1; 5; 10] with ([-9; -6; -3; 1] ++ 5 :: [10]).
        apply Permutation_cons_app.
        simpl.
        change [-9; -6; -3; 1; 10] with ([-9] ++ -6 :: [-3; 1; 10]).
        apply Permutation_cons_app.
        simpl.
        change [-9; -3; 1; 10] with ([-9] ++ -3 :: [1; 10]).
        apply Permutation_cons_app.
        simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_cons; try apply HdRel_nil; try lia]).
        apply Sorted_nil.
Qed.