Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_001 : closest_integer_spec 1 1.
Proof.
  unfold closest_integer_spec.
  (* We need to show that |1 - 1| < 0.5 *)
  (* First, establish that IZR 1 is equal to the real number 1 *)
  replace (IZR 1) with 1 by (simpl; lra).
  (* Simplify the subtraction inside the absolute value *)
  replace (1 - 1) with 0 by lra.
  (* Simplify absolute value of 0 *)
  rewrite Rabs_R0.
  (* We have 0 < 1/2 \/ ..., we choose the left branch *)
  left.
  (* Prove 0 < 1/2 using linear real arithmetic *)
  lra.
Qed.