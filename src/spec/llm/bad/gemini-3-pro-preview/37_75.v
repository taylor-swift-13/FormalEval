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
  [4; 1; 3; 4; 4; 5; 5; 6; 3; 7; 8; 9; -1; 11; 12; 12; 1] 
  [-1; 1; 1; 4; 3; 5; 3; 6; 4; 7; 4; 9; 5; 11; 8; 12; 12].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 17 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [4; 3; 4; 5; 3; 8; -1; 12; 1] [-1; 1; 3; 3; 4; 4; 5; 8; 12] *)
        (* 1. Move 4 *)
        change [-1; 1; 3; 3; 4; 4; 5; 8; 12] with ([-1; 1; 3; 3] ++ 4 :: [4; 5; 8; 12]).
        eapply Permutation_trans. 2: apply Permutation_middle. apply Permutation_cons. simpl.
        (* 2. Move 3 *)
        change [-1; 1; 3; 3; 4; 5; 8; 12] with ([-1; 1] ++ 3 :: [3; 4; 5; 8; 12]).
        eapply Permutation_trans. 2: apply Permutation_middle. apply Permutation_cons. simpl.
        (* 3. Move 4 *)
        change [-1; 1; 3; 4; 5; 8; 12] with ([-1; 1; 3] ++ 4 :: [5; 8; 12]).
        eapply Permutation_trans. 2: apply Permutation_middle. apply Permutation_cons. simpl.
        (* 4. Move 5 *)
        change [-1; 1; 3; 5; 8; 12] with ([-1; 1; 3] ++ 5 :: [8; 12]).
        eapply Permutation_trans. 2: apply Permutation_middle. apply Permutation_cons. simpl.
        (* 5. Move 3 *)
        change [-1; 1; 3; 8; 12] with ([-1; 1] ++ 3 :: [8; 12]).
        eapply Permutation_trans. 2: apply Permutation_middle. apply Permutation_cons. simpl.
        (* 6. Move 8 *)
        change [-1; 1; 8; 12] with ([-1; 1] ++ 8 :: [12]).
        eapply Permutation_trans. 2: apply Permutation_middle. apply Permutation_cons. simpl.
        (* 7. Move -1 *)
        apply perm_skip.
        (* 8. Swap 12 and 1 *)
        apply perm_swap.
        (* 9. Base case *)
        apply perm_nil.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | try (apply HdRel_cons; lia); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.