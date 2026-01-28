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

Example test_sort_even_case : sort_even_spec [2; 3; 2; 9; 3; 6; 7; 8; 2] [2; 3; 2; 9; 2; 6; 3; 8; 7].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Handle indices 0 to 8 explicitly *)
      do 9 (destruct i; [
        simpl in Hodd; try discriminate; simpl; reflexivity
      | ]).
      (* Case i >= 9 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Target: Permutation [2; 2; 3; 7; 2] [2; 2; 2; 3; 7] *)
        apply perm_skip. (* Match first 2 *)
        apply perm_skip. (* Match second 2 *)
        (* Remaining: Permutation [3; 7; 2] [2; 3; 7] *)
        eapply perm_trans.
        { apply perm_skip. apply perm_swap. } (* [3; 7; 2] -> [3; 2; 7] *)
        apply perm_swap. (* [3; 2; 7] -> [2; 3; 7] *)
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons || apply HdRel_cons || apply Sorted_nil || apply HdRel_nil || lia).
Qed.