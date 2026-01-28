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

Example test_sort_even_case : sort_even_spec [5; -5; 2; -3; -9; 0; 123; 1; -10; 2; -3] [-10; -5; -9; -3; -3; 0; 2; 1; 5; 2; 123].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 11 (destruct i; [ simpl in Hodd; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; 2; -9; 123; -10; -3] [-10; -9; -3; 2; 5; 123] *)
        apply Permutation_trans with (l' := 5 :: [-10; -9; -3; 2] ++ [123]).
        2: apply Permutation_middle.
        apply perm_skip.
        simpl.
        
        apply Permutation_trans with (l' := 2 :: [-10; -9; -3] ++ [123]).
        2: apply Permutation_middle.
        apply perm_skip.
        simpl.

        apply Permutation_trans with (l' := -9 :: [-10] ++ [-3; 123]).
        2: apply Permutation_middle.
        apply perm_skip.
        simpl.

        apply Permutation_trans with (l' := 123 :: [-10; -3]).
        2: apply Permutation_middle.
        apply perm_skip.
        simpl.

        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_cons; try apply HdRel_nil; try lia ]).
        apply Sorted_nil.
Qed.