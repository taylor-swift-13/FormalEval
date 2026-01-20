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

Example test_sort_even_case : sort_even_spec [5; -2; -12; 23; 2; 3; 11; 12; 3; 2] [-12; -2; 2; 23; 3; 3; 5; 12; 11; 2].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      repeat (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Target evens: [-12; 2; 3; 5; 11] *)
        (* Source evens: [5; -12; 2; 11; 3] *)
        (* Move 5 (which is at index 3 in target relative to sorted order) to front to match source head *)
        change [-12; 2; 3; 5; 11] with ([-12; 2; 3] ++ 5 :: [11]).
        rewrite Permutation_cons_app.
        simpl.
        (* Remaining: Permutation [-12; 2; 11; 3] [-12; 2; 3; 11] *)
        apply perm_skip.
        (* Remaining: Permutation [2; 11; 3] [2; 3; 11] *)
        apply perm_skip.
        (* Remaining: Permutation [11; 3] [3; 11] *)
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.