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

Example test_sort_even_case : sort_even_spec [5; 3; -10; -5; 2; 3; -9; 1; 0; 123; 1; -10; 12; -4] [-10; 3; -9; -5; 0; 3; 1; 1; 2; 123; 5; -10; 12; -4].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Handle indices 0 to 13 explicitly to avoid timeout/complexity with abstract i *)
      do 14 (destruct i; [
        simpl in Hodd;
        try discriminate; (* For even indices, odd i = false *)
        simpl; reflexivity (* For odd indices, values must match *)
      | ]).
      (* i >= 14 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* List: [5; -10; 2; -9; 0; 1; 12] *)
        (* Target: [-10; -9; 0; 1; 2; 5; 12] *)
        
        (* Move -10 (index 1) to front *)
        etransitivity. apply perm_swap. apply perm_skip.
        
        (* Move -9 (index 2 in tail) to front *)
        etransitivity. apply perm_skip. apply perm_swap.
        etransitivity. apply perm_swap. apply perm_skip.
        
        (* Move 0 (index 2 in tail) to front *)
        etransitivity. apply perm_skip. apply perm_swap.
        etransitivity. apply perm_swap. apply perm_skip.
        
        (* Move 1 (index 2 in tail) to front *)
        etransitivity. apply perm_skip. apply perm_swap.
        etransitivity. apply perm_swap. apply perm_skip.
        
        (* Move 2 (index 1 in tail) to front *)
        etransitivity. apply perm_swap. apply perm_skip.
        
        (* Remaining tail [5; 12] matches [5; 12] *)
        apply Permutation_refl.
        
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.