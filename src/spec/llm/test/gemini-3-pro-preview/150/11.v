Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [-2; 0; 1], output = 1 *)
Example test_x_or_y_neg2 : x_or_y_spec (-2) 0 1 1.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime (-2) -> 1 = 0 *)
    intros Hprime.
    exfalso.
    apply prime_ge_2 in Hprime.
    lia.
  - (* Case: ~ prime (-2) -> 1 = 1 *)
    intros Hnot_prime.
    reflexivity.
Qed.