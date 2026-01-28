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
  [5; -2; -12; 23; 2; 3; 11; 12; -10; 3; 3] 
  [-12; -2; -10; 23; 2; 3; 3; 12; 5; 3; 11].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      repeat (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* LHS: [5; -12; 2; 11; -10; 3] *)
        (* RHS: [-12; -10; 2; 3; 5; 11] *)
        
        (* Move -12 to front *)
        apply perm_trans with (l' := -12 :: [5; 2; 11; -10; 3]).
        { apply perm_swap. }
        apply perm_skip.
        
        (* LHS: [5; 2; 11; -10; 3] *)
        (* RHS: [-10; 2; 3; 5; 11] *)
        
        (* Move -10 to front *)
        apply perm_trans with (l' := -10 :: [5; 2; 11; 3]).
        { 
          change [5; 2; 11; -10; 3] with ([5; 2; 11] ++ [-10] ++ [3]).
          apply Permutation_sym.
          apply Permutation_middle.
        }
        apply perm_skip.
        
        (* LHS: [5; 2; 11; 3] *)
        (* RHS: [2; 3; 5; 11] *)
        
        (* Move 2 to front *)
        apply perm_trans with (l' := 2 :: [5; 11; 3]).
        { apply perm_swap. }
        apply perm_skip.
        
        (* LHS: [5; 11; 3] *)
        (* RHS: [3; 5; 11] *)
        
        (* Move 3 to front (from end) *)
        apply perm_trans with (l' := 3 :: [5; 11]).
        { 
          change [5; 11; 3] with ([5; 11] ++ [3]).
          apply Permutation_sym.
          apply Permutation_cons_append.
        }
        apply perm_skip.
        
        (* LHS: [5; 11] *)
        (* RHS: [5; 11] *)
        apply Permutation_refl.
        
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_cons; try apply HdRel_nil; lia ]).
        apply Sorted_nil.
Qed.