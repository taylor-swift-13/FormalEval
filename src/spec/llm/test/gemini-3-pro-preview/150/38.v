Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [36; 456; 37], output = 37 *)
Example test_x_or_y_36 : x_or_y_spec 36 456 37 37.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 36 -> 37 = 456 *)
    intros Hprime.
    exfalso.
    destruct Hprime as [_ Hrel].
    specialize (Hrel 2).
    assert (1 <= 2 < 36) as Hrange by lia.
    apply Hrel in Hrange.
    rewrite <- Zgcd_1_rel_prime in Hrange.
    vm_compute in Hrange.
    discriminate.
  - (* Case: ~ prime 36 -> 37 = 37 *)
    intros _.
    reflexivity.
Qed.