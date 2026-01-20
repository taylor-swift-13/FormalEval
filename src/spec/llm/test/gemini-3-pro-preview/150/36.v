Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [99; 99; 200], output = 200 *)
Example test_x_or_y_99 : x_or_y_spec 99 99 200 200.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 99 -> 200 = 99 *)
    intros Hprime.
    exfalso.
    destruct Hprime as [_ Hrel].
    assert (H : rel_prime 3 99) by (apply Hrel; lia).
    apply Zgcd_1_rel_prime in H.
    vm_compute in H.
    discriminate.
  - (* Case: ~ prime 99 -> 200 = 200 *)
    intros _.
    reflexivity.
Qed.