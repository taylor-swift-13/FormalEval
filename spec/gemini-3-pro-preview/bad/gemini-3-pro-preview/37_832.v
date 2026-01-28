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

Example test_sort_even_case : 
  sort_even_spec 
    [5; 4; 0; 4; 4; 5; 0; 8; 8; 0; 5] 
    [0; 4; 0; 4; 4; 5; 5; 8; 5; 0; 8].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* We handle indices 0 to 10 explicitly *)
      do 11 (destruct i; [ 
        try (simpl in Hodd; discriminate); try (simpl; reflexivity) 
      | ]).
      (* For indices >= 11 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* LHS: [5; 0; 4; 0; 8; 5] *)
        (* RHS: [0; 0; 4; 5; 5; 8] *)
        
        (* Move first 0 to front *)
        apply Permutation_trans with (l' := [0; 5; 4; 0; 8; 5]).
        { apply perm_swap. }
        apply perm_skip.
        
        (* Current: [5; 4; 0; 8; 5], Target: [0; 4; 5; 5; 8] *)
        (* Move second 0 to front *)
        apply Permutation_trans with (l' := [5; 0; 4; 8; 5]).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := [0; 5; 4; 8; 5]).
        { apply perm_swap. }
        apply perm_skip.
        
        (* Current: [5; 4; 8; 5], Target: [4; 5; 5; 8] *)
        (* Move 4 to front *)
        apply Permutation_trans with (l' := [4; 5; 8; 5]).
        { apply perm_swap. }
        apply perm_skip.
        
        (* Current: [5; 8; 5], Target: [5; 5; 8] *)
        (* Match 5 *)
        apply perm_skip.
        
        (* Current: [8; 5], Target: [5; 8] *)
        (* Swap last two *)
        apply perm_swap.
        apply Permutation_refl.
        
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | constructor; try lia ]).
        apply Sorted_nil.
Qed.