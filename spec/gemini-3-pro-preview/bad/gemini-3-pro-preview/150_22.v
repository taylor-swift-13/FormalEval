Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [62; 40; 20], output = 20 *)
Example test_x_or_y_62 : x_or_y_spec 62 40 20 20.
Proof.
  unfold x_or_y_spec.
  split.
  - intros Hprime.
    exfalso.
    destruct Hprime as [_ Hrel].
    specialize (Hrel 2).
    assert (Hrange: 1 <= 2 < 62) by lia.
    apply Hrel in Hrange.
    unfold rel_prime in Hrange.
    vm_compute in Hrange.
    discriminate Hrange.
  - intros _.
    reflexivity.
Qed.