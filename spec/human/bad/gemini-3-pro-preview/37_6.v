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

Example test_case_37: problem_37_spec [3; 3; 2; 2; 1; 1] [1; 3; 2; 2; 3; 1].
Proof.
  unfold problem_37_spec.
  split.
  - (* Goal 1: Permutation *)
    (* We need to show input is a permutation of output. *)
    (* [3; 3; 2; 2; 1; 1] ~ [1; 3; 2; 2; 3; 1] *)
    apply Permutation_sym.
    (* Goal: [1; 3; 2; 2; 3; 1] ~ [3; 3; 2; 2; 1; 1] *)
    (* Bring 1 to front of RHS *)
    transitivity (1 :: [3; 3; 2; 2; 1]).
    { apply Permutation_sym. apply Permutation_middle. }
    constructor.
    (* Goal: [3; 2; 2; 3; 1] ~ [3; 3; 2; 2; 1] *)
    constructor.
    (* Goal: [2; 2; 3; 1] ~ [3; 2; 2; 1] *)
    (* Bring 3 to front of LHS *)
    transitivity (3 :: [2; 2; 1]).
    { apply Permutation_sym. change [2; 2; 3; 1] with ([2; 2] ++ 3 :: [1]). apply Permutation_middle. }
    (* Goal: [3; 2; 2; 1] ~ [3; 2; 2; 1] *)
    apply Permutation_refl.
  - split.
    + (* Goal 2: Odd indices preservation *)
      intros i Hlen Hodd.
      (* Check i = 0..5 and others *)
      do 6 (destruct i; [ simpl in *; try lia; try reflexivity | ]).
      (* i >= 6 *)
      simpl in Hlen. lia.
    + (* Goal 3: Even indices sorted *)
      intros i j H.
      destruct H as [Hi [Hj [Hie [Hje Hij]]]].
      (* Check i = 0..5 *)
      do 6 (destruct i; [
        (* For each i, check j = 0..5 *)
        do 6 (destruct j; [ simpl in *; try lia | ]);
        (* j >= 6 *)
        simpl in Hj; lia
      | ]).
      (* i >= 6 *)
      simpl in Hi. lia.
Qed.