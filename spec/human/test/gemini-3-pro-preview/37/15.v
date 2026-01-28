Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

(* Use Z scope for integer literals *)
Open Scope Z_scope.

(* Pre: no additional constraints for `sort_even` by default *)
Definition problem_37_pre (input : list Z) : Prop := True.

(* Spec definition with explicit scopes to avoid type errors.
   We explicitly use %nat for nat operations like length, mod, < to avoid
   confusion with Z operations in Z_scope. *)
Definition problem_37_spec (input output : list Z) : Prop :=
  (* 1. input is a permutation of output *)
  Permutation input output /\

  (* 2. If index i is odd, output[i] must equal input[i] *)
  (forall (i : nat), (i < length input)%nat -> (i mod 2 <> 0)%nat ->
    nth i output 0 = nth i input 0) /\

  (* 3. Even indices in output must be sorted *)
  (forall (i j : nat), (i < length output)%nat /\ (j < length output)%nat /\
    (i mod 2 = 0)%nat /\ (j mod 2 = 0)%nat /\ (i < j)%nat ->
    nth i output 0 <= nth j output 0).

Example test_case_37: problem_37_spec 
  [4; 1; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12] 
  [3; 1; 4; 4; 5; 6; 7; 8; 9; 10; 11; 12].
Proof.
  unfold problem_37_spec.
  split.
  - apply perm_trans with (l' := [1; 4; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12]).
    + apply perm_swap.
    + apply perm_trans with (l' := [1; 3; 4; 4; 5; 6; 7; 8; 9; 10; 11; 12]).
      * apply perm_skip. apply perm_swap.
      * apply perm_swap.
  - split.
    + intros i Hlen Hodd.
      do 12 (destruct i as [|i]; [ simpl in *; try lia; try reflexivity | ]).
      simpl in Hlen; lia.
    + intros i j H. destruct H as [Hi [Hj [Hie [Hje Hij]]]].
      do 12 (destruct i as [|i]; [
        do 12 (destruct j as [|j]; [ simpl in *; try lia | ])
        ; simpl in Hj; lia
      | ]).
      simpl in Hi; lia.
Qed.