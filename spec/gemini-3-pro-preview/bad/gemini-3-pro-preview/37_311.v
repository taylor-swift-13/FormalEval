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

Example test_sort_even_case : sort_even_spec [2; 3; 4; 6; 7; 10; 5; 10; 7; 2; 6] [2; 3; 4; 6; 5; 10; 6; 10; 7; 2; 7].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      repeat (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [2; 4; 7; 5; 7; 6] [2; 4; 5; 6; 7; 7] *)
        apply Permutation_cons. (* 2 *)
        apply Permutation_cons. (* 4 *)
        (* Goal: Permutation [7; 5; 7; 6] [5; 6; 7; 7] *)
        transitivity (5 :: [7; 7; 6]).
        { apply Permutation_swap. }
        apply Permutation_cons. (* 5 *)
        (* Goal: Permutation [7; 7; 6] [6; 7; 7] *)
        transitivity (7 :: 6 :: [7]).
        { apply Permutation_cons. apply Permutation_swap. }
        transitivity (6 :: 7 :: [7]).
        { apply Permutation_swap. }
        apply Permutation_cons. (* 6 *)
        apply Permutation_cons. (* 7 *)
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | try (apply HdRel_cons; lia); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.