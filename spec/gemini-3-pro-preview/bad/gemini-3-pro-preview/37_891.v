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
  [5; 3; -10; -5; 2; -2; 3; -9; 1; 0; 123; 1; -10; 12; 12; -5] 
  [-10; 3; -10; -5; 1; -2; 2; -9; 3; 0; 5; 1; 12; 12; 123; -5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      repeat (destruct i as [|i]; [
        simpl in Hodd; try discriminate; simpl; reflexivity
      | ]).
      simpl in Hlen; lia.
    + split.
      * simpl.
        transitivity (5 :: [-10; -10; 1; 2; 3] ++ [12; 123]); [ | apply Permutation_middle ].
        apply Permutation_cons.
        
        apply Permutation_cons.
        
        transitivity (2 :: [-10; 1] ++ [3; 12; 123]); [ | apply Permutation_middle ].
        apply Permutation_cons.
        
        transitivity (3 :: [-10; 1] ++ [12; 123]); [ | apply Permutation_middle ].
        apply Permutation_cons.
        
        transitivity (1 :: [-10] ++ [12; 123]); [ | apply Permutation_middle ].
        apply Permutation_cons.
        
        transitivity (123 :: [-10; 12] ++ []); [ | apply Permutation_middle ].
        apply Permutation_cons.
        
        apply Permutation_cons.
        
        apply Permutation_refl.
      * simpl.
        repeat match goal with
        | |- Sorted _ [] => apply Sorted_nil
        | |- Sorted _ (_ :: _) => apply Sorted_cons
        | |- HdRel _ _ [] => apply HdRel_nil
        | |- HdRel _ _ (_ :: _) => apply HdRel_cons; lia
        end.
Qed.