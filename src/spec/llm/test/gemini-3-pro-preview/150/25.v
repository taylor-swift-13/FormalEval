Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [500; 500; 500], output = 500 *)
Example test_x_or_y_500 : x_or_y_spec 500 500 500 500.
Proof.
  unfold x_or_y_spec.
  split.
  - intros _.
    reflexivity.
  - intros _.
    reflexivity.
Qed.