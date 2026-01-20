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
  [-4; 5; 3; -5; -3; 3; 4; -10; -9; 0; 123; 1; -10] 
  [-10; 5; -9; -5; -4; 3; -3; -10; 3; 0; 4; 1; 123].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 13 (destruct i; [ solve [ simpl in Hodd; discriminate | simpl; reflexivity ] | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Move -10 to front *)
        change ([-4; 3; -3; 4; -9; 123; -10]) with ([-4; 3; -3; 4; -9; 123] ++ [-10]).
        apply Permutation_trans with (-10 :: ([-4; 3; -3; 4; -9; 123] ++ [])).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply perm_skip.

        (* Move -9 to front *)
        change ([-4; 3; -3; 4; -9; 123]) with ([-4; 3; -3; 4] ++ -9 :: [123]).
        apply Permutation_trans with (-9 :: ([-4; 3; -3; 4] ++ [123])).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply perm_skip.

        (* -4 is already at front *)
        apply perm_skip.

        (* Move -3 to front *)
        change ([3; -3; 4; 123]) with ([3] ++ -3 :: [4; 123]).
        apply Permutation_trans with (-3 :: ([3] ++ [4; 123])).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl. apply perm_skip.

        (* 3 is already at front *)
        apply perm_skip.
        
        (* 4 is already at front *)
        apply perm_skip.

        (* 123 is already at front *)
        apply perm_skip.

        (* Nil *)
        apply Permutation_refl.

      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try (apply HdRel_cons; lia); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.