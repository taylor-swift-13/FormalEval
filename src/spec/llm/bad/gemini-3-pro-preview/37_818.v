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
  [11; -5; -7; 2; 10; 0; 9; 5; -5; 2; 8; 3; 7; 9] 
  [-7; -5; -5; 2; 7; 0; 8; 5; 9; 2; 10; 3; 11; 9].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      repeat (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        transitivity (11 :: [-7; -5; 7; 8; 9; 10]).
        2: { apply Permutation_cons_app. rewrite app_nil_r. apply Permutation_refl. }
        apply perm_skip.
        apply perm_skip.
        transitivity (10 :: [-5; 7; 8; 9]).
        2: { apply Permutation_cons_app. rewrite app_nil_r. apply Permutation_refl. }
        apply perm_skip.
        transitivity (9 :: [-5; 7; 8]).
        2: { apply Permutation_cons_app. rewrite app_nil_r. apply Permutation_refl. }
        apply perm_skip.
        apply perm_skip.
        apply Permutation_swap.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_cons; try apply HdRel_nil; try lia]).
        apply Sorted_nil.
Qed.