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

Example test_sort_even_case : sort_even_spec [1; 2; 3; 4; 5; 6; 7; 8; 2] [1; 2; 2; 4; 3; 6; 5; 8; 7].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 9 (destruct i as [|i]; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply perm_skip.
        apply Permutation_sym.
        change (2 :: [3; 5; 7]) with ([2] ++ [3; 5; 7]).
        change (3 :: 5 :: 7 :: 2 :: []) with ([3; 5; 7] ++ [2]).
        apply Permutation_app_comm.
      * simpl.
        apply Sorted_cons; [|apply HdRel_cons; lia].
        apply Sorted_cons; [|apply HdRel_cons; lia].
        apply Sorted_cons; [|apply HdRel_cons; lia].
        apply Sorted_cons; [|apply HdRel_cons; lia].
        apply Sorted_cons; [|apply HdRel_nil].
        apply Sorted_nil.
Qed.