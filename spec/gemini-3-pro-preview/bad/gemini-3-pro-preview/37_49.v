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

Example test_sort_even_case : sort_even_spec [3; 3; 2; 2; 0; 11; 1; 3; 1] [0; 3; 1; 2; 1; 11; 2; 3; 3].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 9 (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [3; 2; 0; 1; 1] [0; 1; 1; 2; 3] *)
        apply (Permutation_trans (l' := 0 :: [3; 2; 1; 1])).
        { apply Permutation_sym. change [3; 2; 0; 1; 1] with ([3; 2] ++ 0 :: [1; 1]). apply Permutation_middle. }
        apply Permutation_cons.
        
        apply (Permutation_trans (l' := 1 :: [3; 2; 1])).
        { apply Permutation_sym. change [3; 2; 1; 1] with ([3; 2] ++ 1 :: [1]). apply Permutation_middle. }
        apply Permutation_cons.
        
        apply (Permutation_trans (l' := 1 :: [3; 2])).
        { apply Permutation_sym. change [3; 2; 1] with ([3; 2] ++ 1 :: []). apply Permutation_middle. }
        apply Permutation_cons.
        
        apply Permutation_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [| try apply HdRel_cons; try apply HdRel_nil; try lia ]).
        apply Sorted_nil.
Qed.