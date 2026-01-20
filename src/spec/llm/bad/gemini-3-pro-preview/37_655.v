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
  [5; 10; -6; 2; -3; 3; -9; 0; 1; -10; 10] 
  [-9; 10; -6; 2; -3; 3; 1; 0; 5; -10; 10].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* We check indices 0 to 10. Odd indices (1, 3, 5, 7, 9) must match. *)
      do 11 (destruct i; [
        (* For the current index, check if odd or even *)
        simpl in Hodd; try discriminate Hodd; simpl; reflexivity
      | ]).
      (* For i >= 11, length check contradicts Hlen *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; -6; -3; -9; 1; 10] [-9; -6; -3; 1; 5; 10] *)
        (* Move -9 to the front *)
        transitivity (-9 :: [5; -6; -3; 1; 10]).
        { 
          change [5; -6; -3; -9; 1; 10] with ([5; -6; -3] ++ -9 :: [1; 10]).
          symmetry. apply Permutation_middle.
        }
        apply perm_skip.
        (* Goal: Permutation [5; -6; -3; 1; 10] [-6; -3; 1; 5; 10] *)
        (* Move -6 to the front *)
        apply perm_swap.
        (* Goal: Permutation [-6; 5; -3; 1; 10] [-6; -3; 1; 5; 10] *)
        apply perm_skip.
        (* Goal: Permutation [5; -3; 1; 10] [-3; 1; 5; 10] *)
        (* Move -3 to the front *)
        apply perm_swap.
        (* Goal: Permutation [-3; 5; 1; 10] [-3; 1; 5; 10] *)
        apply perm_skip.
        (* Goal: Permutation [5; 1; 10] [1; 5; 10] *)
        (* Move 1 to the front *)
        apply perm_swap.
        (* Goal: Permutation [1; 5; 10] [1; 5; 10] *)
        apply perm_skip.
        (* Goal: Permutation [5; 10] [5; 10] *)
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        apply Sorted_cons. { apply HdRel_cons. lia. }
        apply Sorted_cons. { apply HdRel_cons. lia. }
        apply Sorted_cons. { apply HdRel_cons. lia. }
        apply Sorted_cons. { apply HdRel_cons. lia. }
        apply Sorted_cons. { apply HdRel_cons. lia. }
        apply Sorted_cons. { apply HdRel_nil. }
        apply Sorted_nil.
Qed.