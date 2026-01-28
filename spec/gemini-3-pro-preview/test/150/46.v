Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [100; 200; 200], output = 200 *)
Example test_x_or_y_100 : x_or_y_spec 100 200 200 200.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 100 -> 200 = 200 *)
    intros Hprime.
    reflexivity.
  - (* Case: ~ prime 100 -> 200 = 200 *)
    intros Hnot_prime.
    reflexivity.
Qed.