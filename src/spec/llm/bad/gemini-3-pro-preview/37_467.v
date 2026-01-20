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
  [-3; 1; 1; 1; 2; 2; 3; 2; 3; 2; -3; 3] 
  [-3; 1; -3; 1; 1; 2; 2; 2; 3; 2; 3; 3].
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
        apply Permutation_cons.
        apply Permutation_sym.
        change (1 :: 2 :: 3 :: 3 :: -3 :: []) with ([1; 2; 3; 3] ++ [-3]).
        change (-3 :: 1 :: 2 :: 3 :: 3 :: []) with ([-3] ++ [1; 2; 3; 3]).
        apply Permutation_app_comm.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; try lia]).
        apply Sorted_nil.
Qed.