Require Import ZArith.
Require Import Znumtheory. (* For Zmod_divide *)
Open Scope Z_scope.

(* Definition of the specification for the 'multiply' function *)
Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

(* Example proof for the test case: multiply(124, -7) should return 28 *)
Example problem_97_test_1 : problem_97_spec 124 (-7) 28.
Proof.
  unfold problem_97_spec.
  assert (Z.abs 124 mod 10 = 4) as H1.
  { reflexivity. }
  assert (Z.abs (-7) mod 10 = 7) as H2.
  { reflexivity. }
  rewrite H1, H2.
  simpl.
  reflexivity.
Qed.