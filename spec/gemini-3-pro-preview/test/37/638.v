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

Example test_sort_even_case : sort_even_spec 
  [5; 3; -5; -3; 3; -2; -9; 0; 123; -2] 
  [-9; 3; -5; -3; 3; -2; 5; 0; 123; -2].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 10 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        change [-9; -5; 3; 5; 123] with ([-9; -5; 3] ++ 5 :: [123]).
        apply Permutation_cons_app. simpl.
        change [-9; -5; 3; 123] with ([-9] ++ -5 :: [3; 123]).
        apply Permutation_cons_app. simpl.
        change [-9; 3; 123] with ([-9] ++ 3 :: [123]).
        apply Permutation_cons_app. simpl.
        apply Permutation_refl.
      * simpl.
        repeat (constructor; simpl; try lia).
Qed.