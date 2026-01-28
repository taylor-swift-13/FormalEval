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
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12] 
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12].
Proof.
  unfold problem_37_spec.
  split.
  - (* Goal 1: Permutation *)
    apply Permutation_refl.
  - split.
    + (* Goal 2: Odd indices preservation *)
      intros i Hlen Hodd.
      reflexivity.
    + (* Goal 3: Even indices sorted *)
      intros i j H.
      destruct H as [Hi [Hj [Hie [Hje Hij]]]].
      (* Helper assertion to evaluate nth on the concrete list *)
      assert (Hnth: forall n, (n < 12)%nat -> 
        nth n [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12] 0 = Z.of_nat (S n)).
      {
        intros n Hn.
        do 12 (destruct n; [reflexivity |]).
        lia.
      }
      rewrite Hnth by (simpl in *; lia).
      rewrite Hnth by (simpl in *; lia).
      apply Nat2Z.inj_le.
      lia.
Qed.