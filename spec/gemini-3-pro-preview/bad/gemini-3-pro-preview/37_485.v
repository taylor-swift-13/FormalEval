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
  [5; -13; 4; 3; -4; 2; -10; -3; -2; 3; -8; 0; 1; -10; -9; -8] 
  [-10; -13; -9; 3; -8; 2; -4; -3; -2; 3; 1; 0; 4; -10; 5; -8].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 16 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        apply Permutation_sym.
        (* -10 *)
        change [5; 4; -4; -10; -2; -8; 1; -9] with ([5; 4; -4] ++ -10 :: [-2; -8; 1; -9]).
        apply Permutation_cons_app. simpl.
        (* -9 *)
        change [5; 4; -4; -2; -8; 1; -9] with ([5; 4; -4; -2; -8; 1] ++ -9 :: []).
        apply Permutation_cons_app. simpl.
        (* -8 *)
        change [5; 4; -4; -2; -8; 1] with ([5; 4; -4; -2] ++ -8 :: [1]).
        apply Permutation_cons_app. simpl.
        (* -4 *)
        change [5; 4; -4; -2; 1] with ([5; 4] ++ -4 :: [-2; 1]).
        apply Permutation_cons_app. simpl.
        (* -2 *)
        change [5; 4; -2; 1] with ([5; 4] ++ -2 :: [1]).
        apply Permutation_cons_app. simpl.
        (* 1 *)
        change [5; 4; 1] with ([5; 4] ++ 1 :: []).
        apply Permutation_cons_app. simpl.
        (* 4 *)
        change [5; 4] with ([5] ++ 4 :: []).
        apply Permutation_cons_app. simpl.
        (* 5 *)
        change [5] with ([] ++ 5 :: []).
        apply Permutation_cons_app. simpl.
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try lia ]).
        apply Sorted_nil.
Qed.