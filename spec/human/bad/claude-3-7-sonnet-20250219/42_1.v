Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Precondition *)
Definition problem_42_pre (input : list Z) : Prop := True.

(* Specification *)
Definition problem_42_spec(input output : list Z) : Prop :=
  length input = length output /\
  forall i : nat, i < length output -> nth i output 0%Z = (nth i input 0%Z + 1)%Z.

(* Note about test case:
   input = [[]] is a list containing one empty list,
   but our spec expects list Z (integers),
   so we interpret the test case input as [] (empty list),
   and output = [] accordingly. *)

Example problem_42_example :
  problem_42_spec [] [].
Proof.
  unfold problem_42_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    (* i < 0 is false *)
    lia.
Qed.