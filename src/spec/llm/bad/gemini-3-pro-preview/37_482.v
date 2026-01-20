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
  [-5; -7; -6; 2; 10; 0; 9; 5; -3; 2; 8; 7; 2; 8; 2] 
  [-6; -7; -5; 2; -3; 0; 2; 5; 2; 2; 8; 7; 9; 8; 10].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 15 (destruct i; [ try (simpl in Hodd; discriminate); try (simpl; reflexivity) | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        (* Target: [-6; -5; -3; 2; 2; 8; 9; 10] *)
        (* Current: [-5; -6; 10; 9; -3; 8; 2; 2] *)
        
        (* 1. Swap -5 and -6 *)
        apply Permutation_trans with (l' := -6 :: -5 :: 10 :: 9 :: -3 :: 8 :: 2 :: 2).
        { apply Permutation_swap. }
        apply Permutation_cons. apply Permutation_cons.
        
        (* 2. Move -3 to front of [10; 9; -3; 8; 2; 2] *)
        apply Permutation_trans with (l' := -3 :: 10 :: 9 :: 8 :: 2 :: 2).
        { apply Permutation_trans with (l' := 10 :: -3 :: 9 :: 8 :: 2 :: 2).
          - apply Permutation_cons. apply Permutation_swap.
          - apply Permutation_swap. }
        apply Permutation_cons.
        
        (* 3. Move first 2 to front of [10; 9; 8; 2; 2] *)
        apply Permutation_trans with (l' := 2 :: 10 :: 9 :: 8 :: 2).
        { apply Permutation_trans with (l' := 10 :: 9 :: 2 :: 8 :: 2).
          - apply Permutation_cons. apply Permutation_cons. apply Permutation_swap.
          - apply Permutation_trans with (l' := 10 :: 2 :: 9 :: 8 :: 2).
            + apply Permutation_cons. apply Permutation_swap.
            + apply Permutation_swap. }
        apply Permutation_cons.
        
        (* 4. Move second 2 to front of [10; 9; 8; 2] *)
        apply Permutation_trans with (l' := 2 :: 10 :: 9 :: 8).
        { apply Permutation_trans with (l' := 10 :: 9 :: 2 :: 8).
          - apply Permutation_cons. apply Permutation_cons. apply Permutation_swap.
          - apply Permutation_trans with (l' := 10 :: 2 :: 9 :: 8).
            + apply Permutation_cons. apply Permutation_swap.
            + apply Permutation_swap. }
        apply Permutation_cons.
        
        (* 5. Move 8 to front of [10; 9; 8] *)
        apply Permutation_trans with (l' := 8 :: 10 :: 9).
        { apply Permutation_trans with (l' := 10 :: 8 :: 9).
          - apply Permutation_cons. apply Permutation_swap.
          - apply Permutation_swap. }
        apply Permutation_cons.
        
        (* 6. Swap 10 and 9 *)
        apply Permutation_swap.
        
      * simpl.
        repeat match goal with
        | [ |- Sorted _ [] ] => apply Sorted_nil
        | [ |- Sorted _ (_ :: _) ] => apply Sorted_cons
        | [ |- HdRel _ [] ] => apply HdRel_nil
        | [ |- HdRel _ (_ :: _) ] => apply HdRel_cons; lia
        end.
Qed.