Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [25; -26; 25], output = 25 *)
Example test_x_or_y_25 : x_or_y_spec 25 (-26) 25 25.
Proof.
  unfold x_or_y_spec.
  split.
  - intros Hprime.
    exfalso.
    assert (Hdiv: (5 | 25)) by (exists 5; reflexivity).
    pose proof (prime_divisors _ Hprime _ Hdiv) as Hcontra.
    lia.
  - intros Hnot_prime.
    reflexivity.
Qed.