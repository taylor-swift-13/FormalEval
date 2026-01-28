Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [6; 34; 1234], output = 1234 *)
Example test_x_or_y_6 : x_or_y_spec 6 34 1234 1234.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 6 -> 1234 = 34 *)
    intros Hprime.
    exfalso.
    destruct Hprime as [_ Hrel].
    specialize (Hrel 2).
    assert (1 <= 2 < 6) as Hrange by lia.
    specialize (Hrel Hrange).
    unfold rel_prime in Hrel.
    assert (Hgcd: Z.gcd 2 6 = 2) by (vm_compute; reflexivity).
    rewrite Hgcd in Hrel.
    discriminate.
  - (* Case: ~ prime 6 -> 1234 = 1234 *)
    intros _.
    reflexivity.
Qed.