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
  [0; 4; 4; 6; 0; 10; 0; 10; 10] 
  [0; 4; 0; 6; 0; 10; 4; 10; 10].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* We check indices 0 to 8 explicitly to avoid complex destruction logic *)
      do 9 (destruct i as [|i]; [ 
        simpl in Hodd; 
        try discriminate Hodd; (* Filters even indices *)
        simpl; reflexivity (* Checks odd indices equality *)
        | ]).
      (* Case i >= 9, contradiction with length *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [0; 4; 0; 0; 10] [0; 0; 0; 4; 10] *)
        apply perm_skip.
        (* Goal: Permutation [4; 0; 0; 10] [0; 0; 4; 10] *)
        apply Permutation_trans with (l' := 0 :: 4 :: 0 :: 10).
        { apply perm_swap. }
        apply perm_skip.
        (* Goal: Permutation [4; 0; 10] [0; 4; 10] *)
        apply Permutation_trans with (l' := 0 :: 4 :: 10).
        { apply perm_swap. }
        apply perm_skip.
        (* Goal: Permutation [4; 10] [4; 10] *)
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_cons; try apply HdRel_nil; try lia]).
        apply Sorted_nil.
Qed.