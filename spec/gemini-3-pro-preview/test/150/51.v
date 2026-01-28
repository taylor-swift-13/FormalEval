Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [99; 99; 99], output = 99 *)
Example test_x_or_y_99 : x_or_y_spec 99 99 99 99.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 99 -> 99 = 99 *)
    intros _.
    reflexivity.
  - (* Case: ~ prime 99 -> 99 = 99 *)
    intros _.
    reflexivity.
Qed.