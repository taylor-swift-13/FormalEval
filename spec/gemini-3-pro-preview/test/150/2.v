Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [15; 8; 5], output = 5 *)
Example test_x_or_y_15 : x_or_y_spec 15 8 5 5.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 15 -> 5 = 8 *)
    intros Hprime.
    exfalso.
    (* Prove contradiction: 15 is not prime because 3 divides 15 *)
    assert (Hdiv: (3 | 15)) by (exists 5; lia).
    pose proof (prime_divisors _ Hprime _ Hdiv) as Hcontra.
    lia.
  - (* Case: ~ prime 15 -> 5 = 5 *)
    intros _.
    reflexivity.
Qed.