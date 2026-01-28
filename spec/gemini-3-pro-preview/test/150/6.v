Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [3609; 1245; 583], output = 583 *)
Example test_x_or_y_3609 : x_or_y_spec 3609 1245 583 583.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 3609 -> 583 = 1245 *)
    intros Hprime.
    exfalso.
    destruct Hprime as [_ Hrel].
    specialize (Hrel 3).
    assert (Hcond: 1 <= 3 < 3609) by lia.
    apply Hrel in Hcond.
    pose proof (Zgcd_is_gcd 3 3609) as Hreal.
    pose proof (Zis_gcd_unique _ _ _ _ Hcond Hreal) as [Heq | Heq];
      vm_compute in Heq; discriminate Heq.
  - (* Case: ~ prime 3609 -> 583 = 583 *)
    intros _.
    reflexivity.
Qed.