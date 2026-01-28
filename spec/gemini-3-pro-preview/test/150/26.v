Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [62; 40; 62], output = 62 *)
Example test_x_or_y_62 : x_or_y_spec 62 40 62 62.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 62 -> 62 = 40 *)
    intros Hprime.
    exfalso.
    inversion Hprime as [_ Hforall].
    specialize (Hforall 2).
    assert (1 <= 2 < 62) as Hrange by lia.
    specialize (Hforall Hrange).
    apply Zgcd_1_rel_prime in Hforall.
    vm_compute in Hforall.
    lia.
  - (* Case: ~ prime 62 -> 62 = 62 *)
    intros Hnot_prime.
    reflexivity.
Qed.