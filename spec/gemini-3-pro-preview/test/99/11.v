Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition closest_integer_spec (val : R) (result : Z) : Prop :=
  let dist := Rabs (val - IZR result) in
  (dist < / 2) \/
  (dist = / 2 /\ Rabs (IZR result) > Rabs val).

Example test_case_1_6 : closest_integer_spec 1.6 2.
Proof.
  unfold closest_integer_spec.
  left.
  (* Establish that IZR 2 is equal to the real number 2 *)
  replace (IZR 2) with 2 by (simpl; lra).
  (* We need to show Rabs (1.6 - 2) < 0.5 *)
  (* 1.6 - 2 = -0.4. Since -0.4 < 0, Rabs (-0.4) = -(-0.4) = 0.4 *)
  rewrite Rabs_left; lra.
Qed.