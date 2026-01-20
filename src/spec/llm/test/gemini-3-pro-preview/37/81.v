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

Example test_sort_even_case : sort_even_spec [4; 1; 1; 3; 4; 5; 6; 3; 7; 8; 5; 9; 10; 11; 10] [1; 1; 4; 3; 4; 5; 5; 3; 6; 8; 7; 9; 10; 11; 10].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 15 (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* LHS: [4; 1; 4; 6; 7; 5; 10; 10] *)
        (* RHS: [1; 4; 4; 5; 6; 7; 10; 10] *)
        apply perm_trans with (l' := [1; 4; 4; 6; 7; 5; 10; 10]).
        { apply perm_swap. }
        apply perm_skip. apply perm_skip. apply perm_skip.
        apply perm_trans with (l' := [6; 5; 7; 10; 10]).
        { apply perm_skip. apply perm_swap. }
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; apply HdRel_cons; lia ]).
        apply Sorted_nil.
Qed.