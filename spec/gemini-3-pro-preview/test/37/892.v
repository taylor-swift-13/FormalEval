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

Example test_sort_even_case : sort_even_spec [1; 1; 23; 1; 0; 8; 1; 1] [0; 1; 1; 1; 1; 8; 23; 1].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* We check indices 0 to 7 explicitly. For i >= 8, Hlen gives a contradiction. *)
      do 8 (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [1; 23; 0; 1] [0; 1; 1; 23] *)
        (* We sort the left list step by step to match the right list using transitivity and swap *)
        eapply Permutation_trans.
        apply perm_skip. apply perm_swap. (* Swap 23 and 0 -> [1; 0; 23; 1] *)
        eapply Permutation_trans.
        apply perm_swap. (* Swap 1 and 0 -> [0; 1; 23; 1] *)
        (* Now head is 0, match it *)
        apply perm_skip.
        (* Goal: Permutation [1; 23; 1] [1; 1; 23] *)
        apply perm_skip.
        (* Goal: Permutation [23; 1] [1; 23] *)
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat (constructor; try lia).
Qed.