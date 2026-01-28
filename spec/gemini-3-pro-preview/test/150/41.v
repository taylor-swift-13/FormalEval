Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [500; 500; 501], output = 501 *)
Example test_x_or_y_500 : x_or_y_spec 500 500 501 501.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 500 -> 501 = 500 *)
    intros Hprime.
    exfalso.
    (* 500 is not prime because 2 divides it *)
    assert (Hdiv: (2 | 500)) by (exists 250; reflexivity).
    apply prime_divisors with (a := 2) in Hprime; [| assumption].
    lia.
  - (* Case: ~ prime 500 -> 501 = 501 *)
    intros _.
    reflexivity.
Qed.