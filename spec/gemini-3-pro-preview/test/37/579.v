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

Example test_sort_even_case : sort_even_spec [122; 4; 3; 2; -4; -11; 3; 3] [-4; 4; 3; 2; 3; -11; 122; 3].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Check indices 0 to 7 explicitly to avoid timeout/complexity with symbolic execution *)
      do 8 (destruct i; [ 
        simpl in Hodd; 
        try discriminate Hodd; (* Discard even indices *)
        simpl; reflexivity     (* Check odd indices values *)
        | ]).
      (* For i >= 8 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [122; 3; -4; 3] [-4; 3; 3; 122] *)
        (* Manually construct the permutation to guide the proof *)
        apply Permutation_trans with (l' := [122; -4; 3; 3]).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := [-4; 122; 3; 3]).
        { apply perm_swap. }
        apply Permutation_trans with (l' := [-4; 3; 122; 3]).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := [-4; 3; 3; 122]).
        { apply perm_skip. apply perm_skip. apply perm_swap. }
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        (* Verify [-4; 3; 3; 122] is sorted *)
        repeat (apply Sorted_cons; [ | try apply HdRel_cons; try apply HdRel_nil; try lia ]).
        apply Sorted_nil.
Qed.