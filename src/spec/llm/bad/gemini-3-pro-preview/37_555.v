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
  [-6; 5; -13; 3; -5; 2; -10; -3; -2; 3; -8; 0; 1; -10; -9; -8] 
  [-13; 5; -10; 3; -9; 2; -8; -3; -6; 3; -5; 0; -2; -10; 1; -8].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      repeat (destruct i; [ simpl in Hodd; try discriminate; simpl; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        apply Permutation_sym.
        apply Permutation_trans with (l' := -13 :: [-6] ++ [-5; -10; -2; -8; 1; -9]); [ apply perm_skip | apply Permutation_middle ]. simpl.
        apply Permutation_trans with (l' := -10 :: [-6; -5] ++ [-2; -8; 1; -9]); [ apply perm_skip | apply Permutation_middle ]. simpl.
        apply Permutation_trans with (l' := -9 :: [-6; -5; -2; -8; 1] ++ []); [ apply perm_skip | apply Permutation_middle ]. simpl.
        apply Permutation_trans with (l' := -8 :: [-6; -5; -2] ++ [1]); [ apply perm_skip | apply Permutation_middle ]. simpl.
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat constructor; simpl; try lia.
Qed.