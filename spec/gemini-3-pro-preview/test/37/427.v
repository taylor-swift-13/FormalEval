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

Example test_sort_even_case : sort_even_spec [-3; 2; 2; 3; 4; 6; 7; 122; 123; 8; 2; 8] [-3; 2; 2; 3; 2; 6; 4; 122; 7; 8; 123; 8].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* We check indices 0 to 11. For i >= 12, Hlen provides a contradiction. *)
      do 12 (destruct i; [ simpl in Hodd; try discriminate; simpl; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Reduce the problem by removing matching heads *)
        apply perm_skip. (* -3 *)
        apply perm_skip. (* 2 *)
        (* Remaining: Permutation [4; 7; 123; 2] [2; 4; 7; 123] *)
        (* This corresponds to moving the last element (2) to the front *)
        change [4; 7; 123; 2] with ([4; 7; 123] ++ [2]).
        change [2; 4; 7; 123] with ([2] ++ [4; 7; 123]).
        apply Permutation_app_comm.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [| try apply HdRel_nil; try (apply HdRel_cons; simpl; lia)]).
        apply Sorted_nil.
Qed.