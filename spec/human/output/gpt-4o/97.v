Require Import ZArith.
Require Import Znumtheory. (* For Zmod_divide *)
Open Scope Z_scope.

(* Definition of the specification for the 'multiply' function *)
Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

(* Example proof for the test case: multiply(148, 412) should return 16 *)
Example problem_97_test_1 : problem_97_spec 148 412 16.
Proof.
  unfold problem_97_spec.
  (* Calculate the absolute values and mod 10 for each input *)
  assert (Z.abs 148 mod 10 = 8) as H1.
  { reflexivity. }
  assert (Z.abs 412 mod 10 = 2) as H2.
  { reflexivity. }
  (* Multiply the results *)
  rewrite H1, H2.
  simpl.
  reflexivity.
Qed.