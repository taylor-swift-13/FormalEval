Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [0; 500; 1000], output = 1000 *)
Example test_x_or_y_0 : x_or_y_spec 0 500 1000 1000.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 0 -> 1000 = 500 *)
    intros Hprime.
    exfalso.
    apply prime_ge_2 in Hprime.
    lia.
  - (* Case: ~ prime 0 -> 1000 = 1000 *)
    intros Hnot_prime.
    reflexivity.
Qed.