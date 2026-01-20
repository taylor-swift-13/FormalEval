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
  [5; -3; 3; -5; 2; -3; 3; -9; 123; 1; -10; 10; -5; 3] 
  [-10; -3; -5; -5; 2; -3; 3; -9; 3; 1; 5; 10; 123; 3].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 14 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        apply Permutation_sym.
        change [5; 3; 2; 3; 123; -10; -5] with ([5; 3; 2; 3; 123] ++ -10 :: [-5]).
        apply Permutation_cons_app. simpl.
        change [5; 3; 2; 3; 123; -5] with ([5; 3; 2; 3; 123] ++ -5 :: []).
        apply Permutation_cons_app. simpl.
        change [5; 3; 2; 3; 123] with ([5; 3] ++ 2 :: [3; 123]).
        apply Permutation_cons_app. simpl.
        change [5; 3; 3; 123] with ([5] ++ 3 :: [3; 123]).
        apply Permutation_cons_app. simpl.
        change [5; 3; 123] with ([5] ++ 3 :: [123]).
        apply Permutation_cons_app. simpl.
        apply Permutation_cons_app. simpl.
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [| simpl; try lia]).
        apply Sorted_nil.
Qed.