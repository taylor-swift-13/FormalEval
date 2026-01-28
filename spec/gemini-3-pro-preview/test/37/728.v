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

Example test_sort_even_case : sort_even_spec [5; 4; 4; 5; 0; 8; 0; 5] [0; 4; 0; 5; 4; 8; 5; 5].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Check each index 0..7 *)
      do 8 (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      (* Handle out of bounds *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; 4; 0; 0] [0; 0; 4; 5] *)
        (* Manually sort using swaps *)
        apply Permutation_trans with (l' := [4; 5; 0; 0]).
        { apply perm_swap. }
        apply Permutation_trans with (l' := [4; 0; 5; 0]).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := [4; 0; 0; 5]).
        { apply perm_skip. apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := [0; 4; 0; 5]).
        { apply perm_swap. }
        apply Permutation_trans with (l' := [0; 0; 4; 5]).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (constructor; try lia).
Qed.