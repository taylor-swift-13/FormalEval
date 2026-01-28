Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_10 : closest_integer_spec 10 10.
Proof.
  unfold closest_integer_spec.
  (* We need to show that |10 - 10| < 0.5 *)
  (* First, establish that IZR 10 is equal to the real number 10 *)
  replace (IZR 10) with 10 by (simpl; lra).
  (* Simplify the subtraction inside the absolute value *)
  replace (10 - 10) with 0 by lra.
  (* Simplify absolute value of 0 *)
  rewrite Rabs_R0.
  (* We have 0 < 1/2 \/ ..., we choose the left branch *)
  left.
  (* Prove 0 < 1/2 using linear real arithmetic *)
  lra.
Qed.