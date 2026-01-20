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
  [-5; -7; 2; 10; 0; 9; 5; -3; 2; 8; 3; 7; 2; 8] 
  [-5; -7; 0; 10; 2; 9; 2; -3; 2; 8; 3; 7; 5; 8].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Handle indices 0 to 13 *)
      do 14 (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      (* Indices >= 14 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* LHS: -5; 2; 0; 5; 2; 3; 2 *)
        (* RHS: -5; 0; 2; 2; 2; 3; 5 *)
        apply perm_skip. (* -5 *)
        apply perm_trans with (l' := 0 :: 2 :: [5; 2; 3; 2]). apply perm_swap. apply perm_skip. (* 0 *)
        apply perm_skip. (* 2 *)
        apply perm_trans with (l' := 2 :: 5 :: [3; 2]). apply perm_swap. apply perm_skip. (* 2 *)
        apply perm_trans with (l' := 5 :: 2 :: [3]). apply perm_skip. apply perm_swap.
        apply perm_trans with (l' := 2 :: 5 :: [3]). apply perm_swap. apply perm_skip. (* 2 *)
        apply perm_swap. (* 3 and 5 *)
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | try (apply HdRel_cons; lia); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.