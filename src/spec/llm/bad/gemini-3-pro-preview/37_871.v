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
    [5; 3; 10; -5; 2; -3; 3; -9; 0; 123; 1; -10; 1; 10; -5; 0] 
    [-5; 3; 0; -5; 1; -3; 1; -9; 2; 123; 3; -10; 5; 10; 10; 0].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 16 (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply (Permutation_cons_app _ _ [-5; 0; 1; 1; 2; 3] [10]). simpl.
        apply (Permutation_cons_app _ _ [-5; 0; 1; 1; 2; 3] []). simpl.
        apply (Permutation_cons_app _ _ [-5; 0; 1; 1] [3]). simpl.
        apply (Permutation_cons_app _ _ [-5; 0; 1; 1] []). simpl.
        apply (Permutation_cons_app _ _ [-5] [1; 1]). simpl.
        apply (Permutation_cons_app _ _ [-5] [1]). simpl.
        apply (Permutation_cons_app _ _ [-5] []). simpl.
        apply (Permutation_cons_app _ _ [] []). simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; first [ apply HdRel_nil | apply HdRel_cons; lia ] ]).
        apply Sorted_nil.
Qed.