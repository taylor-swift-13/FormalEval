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
  [-5; -7; 2; 10; 0; 9; 5; -3; 2; 8; 3; 7; 2; -3] 
  [-5; -7; 0; 10; 2; 9; 2; -3; 2; 8; 3; 7; 5; -3].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Check i = 0..13 *)
      do 14 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      (* i >= 14 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* L: [-5; 2; 0; 5; 2; 3; 2] *)
        (* R: [-5; 0; 2; 2; 2; 3; 5] *)
        apply perm_skip.
        (* L: [2; 0; 5; 2; 3; 2] *)
        apply (Permutation_trans (0 :: 2 :: 5 :: 2 :: 3 :: 2 :: [])).
        { apply perm_swap. }
        apply perm_skip.
        (* L: [2; 5; 2; 3; 2] *)
        apply perm_skip.
        (* L: [5; 2; 3; 2] *)
        apply (Permutation_trans (2 :: 5 :: 3 :: 2 :: [])).
        { apply perm_swap. }
        apply perm_skip.
        (* L: [5; 3; 2] *)
        (* Target R: [2; 3; 5] *)
        apply (Permutation_trans (2 :: 5 :: 3 :: [])).
        { apply (Permutation_trans (5 :: 2 :: 3 :: [])).
          - apply perm_skip. apply perm_swap.
          - apply perm_swap. }
        apply perm_skip.
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try apply HdRel_cons; try lia ]).
        apply Sorted_nil.
Qed.