Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [49; 3; 3], output = 3 *)
Example test_x_or_y_49 : x_or_y_spec 49 3 3 3.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 49 -> 3 = 3 *)
    intros Hprime.
    reflexivity.
  - (* Case: ~ prime 49 -> 3 = 3 *)
    intros Hnot_prime.
    reflexivity.
Qed.