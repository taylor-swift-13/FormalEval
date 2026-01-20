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
  [6; 3; 6; 1; 4; 1; 5; 9; 2; 6; 5; 3; 6] 
  [2; 3; 4; 1; 5; 1; 5; 9; 6; 6; 6; 3; 6].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* We destruct i for each index 0..12 to check conditions *)
      do 13 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      (* Case i >= 13 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* We use symmetry to sort the right-hand side (unsorted) into the left-hand side (sorted) *)
        apply Permutation_sym.
        (* Move 2 to front *)
        apply perm_trans with (2 :: [6; 6; 4; 5; 5; 6]).
        { apply Permutation_middle. }
        constructor.
        (* Move 4 to front *)
        apply perm_trans with (4 :: [6; 6; 5; 5; 6]).
        { apply Permutation_middle. }
        constructor.
        (* Move 5 to front *)
        apply perm_trans with (5 :: [6; 6; 5; 6]).
        { apply Permutation_middle. }
        constructor.
        (* Move 5 to front *)
        apply perm_trans with (5 :: [6; 6; 6]).
        { apply Permutation_middle. }
        constructor.
        (* The rest [6; 6; 6] is already in order *)
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat constructor; try lia.
Qed.