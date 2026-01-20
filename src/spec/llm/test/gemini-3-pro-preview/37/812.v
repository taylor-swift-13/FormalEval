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
  [-7; 2; 10; 0; 9; 5; 12; 2; 8; 3; 7; 9] 
  [-7; 2; 7; 0; 8; 5; 9; 2; 10; 3; 12; 9].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 12 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply perm_skip.
        change [10; 9; 12; 8; 7] with ([10; 9; 12; 8] ++ [7]).
        change (7 :: [10; 9; 12; 8]) with ([7] ++ [10; 9; 12; 8]).
        transitivity ([7] ++ [10; 9; 12; 8]).
        { apply Permutation_app_comm. }
        simpl. apply perm_skip.
        change [10; 9; 12; 8] with ([10; 9; 12] ++ [8]).
        change (8 :: [10; 9; 12]) with ([8] ++ [10; 9; 12]).
        transitivity ([8] ++ [10; 9; 12]).
        { apply Permutation_app_comm. }
        simpl. apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | first [ apply HdRel_cons; lia | apply HdRel_nil ] ]).
        apply Sorted_nil.
Qed.