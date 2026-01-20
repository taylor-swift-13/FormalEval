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
  [2; 2; 3; 123; 6; 7; 8; 2; 2; 7; 2] 
  [2; 2; 2; 123; 2; 7; 3; 2; 6; 7; 8].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* We use destruct i as [|i] to preserve the variable name i for the next iteration *)
      do 11 (destruct i as [|i]; [ 
        try (simpl in Hodd; discriminate Hodd); 
        try (simpl; reflexivity) 
      | ]).
      (* Case i >= 11, which contradicts length = 11 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* LHS evens: [2; 3; 6; 8; 2; 2] *)
        (* RHS evens: [2; 2; 2; 3; 6; 8] *)
        apply Permutation_cons. (* Matches first 2 *)
        (* Goal: Permutation [3; 6; 8; 2; 2] [2; 2; 3; 6; 8] *)
        (* Move last 2 of LHS to front *)
        change ([3; 6; 8; 2; 2]) with ([3; 6; 8; 2] ++ [2]).
        eapply Permutation_trans.
        { apply Permutation_app_comm. }
        (* LHS is now [2; 3; 6; 8; 2] *)
        simpl. apply Permutation_cons. (* Matches second 2 *)
        (* Goal: Permutation [3; 6; 8; 2] [2; 3; 6; 8] *)
        (* Move last 2 of LHS to front *)
        change ([3; 6; 8; 2]) with ([3; 6; 8] ++ [2]).
        eapply Permutation_trans.
        { apply Permutation_app_comm. }
        (* LHS is now [2; 3; 6; 8] *)
        simpl. apply Permutation_cons. (* Matches third 2 *)
        (* Goal: Permutation [3; 6; 8] [3; 6; 8] *)
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (constructor; try lia).
Qed.