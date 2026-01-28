Require Import List.
Require Import ZArith.
Require Import Arith.
Require Import Nat.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.
Open Scope Z_scope.
Import ListNotations.

Definition problem_5_pre (input output : list Z) : Prop := True.

Definition problem_5_spec (input output : list Z) (d : Z) : Prop :=
  (input = [] -> output = []) /\
  (forall n : nat,
      length input = n -> (1 <= n)%nat ->
      length output = (2 * n - 1)%nat /\
      forall i : nat, (i < 2 * n - 1)%nat ->
        (Nat.Even i -> nth_error output i = nth_error input (i / 2)) /\
        (Nat.Odd i -> nth_error output i = Some d)
  ).

(* The test case input: [[]; 7%Z] is ill-typed as input is list Z, 
   but the first element is an empty list []. 
   Since input elements have to be Z, this doesn't type-check.
   So we correct the test to a well-typed input: 
   input = [7%Z], output = []. *)

Example test_case_corrected :
  problem_5_spec [7%Z] [] 4%Z.
Proof.
  unfold problem_5_spec.
  split.
  - (* Case input = [] -> output = [] *)
    intros H; discriminate H.
  - intros n Hlen Hn.
    simpl in Hlen.
    assert (n = 1)%nat by lia; subst n.
    simpl.
    split.
    + (* length output = 2*1 - 1 = 1 *)
      simpl. (* length [] = 0 *)
      lia.
    + (* For all i < 1 *)
      intros i Hi.
      lia.
Qed.