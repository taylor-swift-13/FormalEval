Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [41; 20; 20], output = 20 *)
Example test_x_or_y_41 : x_or_y_spec 41 20 20 20.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 41 -> 20 = 20 *)
    intros Hprime.
    reflexivity.
  - (* Case: ~ prime 41 -> 20 = 20 *)
    intros Hnot_prime.
    reflexivity.
Qed.