Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Sorting.Sorted.
Import ListNotations.

(* The specification given uses Sorted with Nat.lt (strictly increasing).
   The test case input = [[5%Z]] means list [5], output = true.

   We'll prove the problem_126_spec for l = [5] and b = true.

   Note: no boolean function with _ && _ is present in the spec as given,
   so we don't use boolean connectives here.

   Also, problem_126_spec is:
   Sorted Nat.lt l <-> b = true.
*)

Definition problem_126_pre (l : list nat) : Prop := True.

Definition problem_126_spec (l : list nat) (b : bool) : Prop :=
  (Sorted Nat.lt l <-> b = true).

Example test_case_1 : 
  problem_126_spec [5] true.
Proof.
  unfold problem_126_spec.
  simpl.
  split.
  - intros H.
    reflexivity.
  - intros H.
    (* Show Sorted Nat.lt [5] *)
    unfold Sorted.
    constructor.
Qed.
Qed.