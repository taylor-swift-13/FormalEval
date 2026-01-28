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

Example test_case_37: problem_37_spec [5; 8; -12; 4; 23; 2; 3; 11; 12; -10] [-12; 8; 3; 4; 5; 2; 12; 11; 23; -10].
Proof.
  unfold problem_37_spec.
  split.
  - (* Goal 1: Permutation *)
    (* Since the lists contain distinct concrete values, we use NoDup_Permutation *)
    apply NoDup_Permutation.
    + (* NoDup input *)
      repeat (constructor; [ intro H; simpl in H; repeat destruct H as [H|H]; try lia | ]).
      constructor.
    + (* NoDup output *)
      repeat (constructor; [ intro H; simpl in H; repeat destruct H as [H|H]; try lia | ]).
      constructor.
    + (* Equivalence of elements *)
      intros x; simpl; split; intro H; repeat destruct H as [H|H]; subst; simpl; auto 20.
  - split.
    + (* Goal 2: Odd indices preservation *)
      intros i Hlen Hodd.
      (* Destruct i to cover all indices 0..9. do 11 covers 0..10 and closes the rest. *)
      do 11 (destruct i as [|i]; [ try (simpl in *; lia); try (simpl; reflexivity) | ]).
      simpl in Hlen; lia.
    + (* Goal 3: Even indices sorted *)
      intros i j H.
      destruct H as [Hi [Hj [Hie [Hje Hij]]]].
      (* Nested destruct to check all pairs of indices *)
      do 11 (destruct i as [|i]; [
        do 11 (destruct j as [|j]; [
           try (simpl in *; lia)
        | ]); simpl in Hj; lia
      | ]).
      simpl in Hi; lia.
Qed.