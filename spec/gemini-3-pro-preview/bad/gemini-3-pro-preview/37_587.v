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
  [-3; 2; 2; 3; 4; 6; 7; 122; 123; 8; 8; 2; 7; 4; 8] 
  [-3; 2; 2; 3; 4; 6; 7; 122; 7; 8; 8; 2; 8; 4; 123].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 15 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        apply perm_skip. apply perm_skip. apply perm_skip. apply perm_skip.
        apply Permutation_sym.
        apply Permutation_trans with (l' := 7 :: [123; 8; 8]).
        2: {
          change [123; 8; 7; 8] with ([123; 8] ++ 7 :: [8]).
          change (7 :: [123; 8; 8]) with (7 :: [123; 8] ++ [8]).
          apply Permutation_middle.
        }
        apply perm_skip.
        apply Permutation_trans with (l' := 8 :: [123; 8]).
        2: {
          change [123; 8; 8] with ([123] ++ 8 :: [8]).
          change (8 :: [123; 8]) with (8 :: [123] ++ [8]).
          apply Permutation_middle.
        }
        apply perm_skip.
        apply Permutation_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat constructor.
        all: simpl; try lia.
Qed.