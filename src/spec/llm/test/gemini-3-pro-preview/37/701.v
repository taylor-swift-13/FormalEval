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
  [5; 3; -5; 23; -3; 3; -9; 0; 123; -1; -10] 
  [-10; 3; -9; 23; -5; 3; -3; 0; 5; -1; 123].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 11 (destruct i as [|i]; [ 
        simpl in Hodd; try discriminate Hodd; simpl; reflexivity 
      | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        transitivity ([-10; -9; -5; -3] ++ 5 :: [123]).
        2: apply Permutation_refl.
        apply Permutation_cons_app.
        
        transitivity ([-10; -9] ++ -5 :: [-3; 123]).
        2: apply Permutation_refl.
        apply Permutation_cons_app.
        
        transitivity ([-10; -9] ++ -3 :: [123]).
        2: apply Permutation_refl.
        apply Permutation_cons_app.
        
        transitivity ([-10] ++ -9 :: [123]).
        2: apply Permutation_refl.
        apply Permutation_cons_app.
        
        transitivity ([-10] ++ 123 :: []).
        2: apply Permutation_refl.
        apply Permutation_cons_app.
        
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [| try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.