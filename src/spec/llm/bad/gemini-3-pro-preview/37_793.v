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
    [5; 4; 4; 5; 4; 0; 8; 8; 0; 5; 4] 
    [0; 4; 4; 5; 4; 0; 4; 8; 5; 5; 8].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      repeat (destruct i as [|i]; [ 
        simpl in *; try discriminate Hodd; try reflexivity 
      | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; 4; 4; 8; 0; 4] [0; 4; 4; 4; 5; 8] *)
        transitivity (0 :: [5; 4; 4; 8] ++ [4]).
        { change [5; 4; 4; 8; 0; 4] with ([5; 4; 4; 8] ++ 0 :: [4]).
          apply Permutation_sym, Permutation_middle. }
        apply Permutation_cons.
        
        simpl.
        (* Goal: Permutation [5; 4; 4; 8; 4] [4; 4; 4; 5; 8] *)
        transitivity (4 :: [5] ++ [4; 8; 4]).
        { change [5; 4; 4; 8; 4] with ([5] ++ 4 :: [4; 8; 4]).
          apply Permutation_sym, Permutation_middle. }
        apply Permutation_cons.
        
        simpl.
        (* Goal: Permutation [5; 4; 8; 4] [4; 4; 5; 8] *)
        transitivity (4 :: [5] ++ [8; 4]).
        { change [5; 4; 8; 4] with ([5] ++ 4 :: [8; 4]).
          apply Permutation_sym, Permutation_middle. }
        apply Permutation_cons.
        
        simpl.
        (* Goal: Permutation [5; 8; 4] [4; 5; 8] *)
        transitivity (4 :: [5; 8] ++ []).
        { change [5; 8; 4] with ([5; 8] ++ 4 :: []).
          apply Permutation_sym, Permutation_middle. }
        apply Permutation_cons.
        
        simpl.
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.