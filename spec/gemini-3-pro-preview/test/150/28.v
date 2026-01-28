Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [123; 499; 500], output = 500 *)
Example test_x_or_y_123 : x_or_y_spec 123 499 500 500.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 123 -> 500 = 499 *)
    intros Hprime.
    exfalso.
    destruct Hprime as [_ Hrel].
    specialize (Hrel 3).
    assert (1 <= 3 < 123) as Hrange by lia.
    specialize (Hrel Hrange).
    apply Zgcd_1_rel_prime in Hrel.
    vm_compute in Hrel.
    discriminate.
  - (* Case: ~ prime 123 -> 500 = 500 *)
    intros _.
    reflexivity.
Qed.