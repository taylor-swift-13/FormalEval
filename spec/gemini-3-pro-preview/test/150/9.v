Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [1; 2; 0], output = 0 *)
Example test_x_or_y_1 : x_or_y_spec 1 2 0 0.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 1 -> 0 = 2 *)
    intros Hprime.
    exfalso.
    (* prime p implies 1 < p, so prime 1 implies 1 < 1 which is false *)
    inversion Hprime.
    lia.
  - (* Case: ~ prime 1 -> 0 = 0 *)
    intros Hnot_prime.
    reflexivity.
Qed.