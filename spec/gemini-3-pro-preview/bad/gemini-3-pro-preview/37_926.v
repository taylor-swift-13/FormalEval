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
  [5; 3; -5; -2; 3; -9; 1; 0; 123; 1; 9; -10; 12; 123] 
  [-5; 3; 1; -2; 3; -9; 5; 0; 9; 1; 12; -10; 123; 123].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* The list has length 14. We destruct i 14 times to handle indices 0..13 *)
      do 14 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      (* Remaining indices >= 14 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* L1: [5; -5; 3; 1; 123; 9; 12] *)
        (* L2: [-5; 1; 3; 5; 9; 12; 123] *)
        etransitivity.
        { apply perm_swap. } 
        apply perm_skip.
        (* [5; 3; 1; 123; 9; 12] vs [1; 3; 5; 9; 12; 123] *)
        etransitivity.
        { apply perm_skip. apply perm_swap. } 
        etransitivity.
        { apply perm_swap. } 
        apply perm_skip.
        (* [5; 3; 123; 9; 12] vs [3; 5; 9; 12; 123] *)
        etransitivity.
        { apply perm_swap. } 
        apply perm_skip.
        (* [5; 123; 9; 12] vs [5; 9; 12; 123] *)
        apply perm_skip.
        (* [123; 9; 12] vs [9; 12; 123] *)
        etransitivity.
        { apply perm_swap. } 
        apply perm_skip.
        (* [123; 12] vs [12; 123] *)
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat (constructor; [ | try lia ]).
Qed.