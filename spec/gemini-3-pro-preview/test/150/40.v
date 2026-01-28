Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [100; 456; 99], output = 99 *)
Example test_x_or_y_100 : x_or_y_spec 100 456 99 99.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 100 -> 99 = 456 *)
    intros Hprime.
    exfalso.
    assert (Hdiv: (2 | 100)) by (exists 50; reflexivity).
    apply prime_divisors with (1 := Hprime) in Hdiv.
    destruct Hdiv as [H1 | H2]; lia.
  - (* Case: ~ prime 100 -> 99 = 99 *)
    intros Hnot_prime.
    reflexivity.
Qed.