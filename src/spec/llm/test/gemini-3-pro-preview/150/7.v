Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [91; 56; 129], output = 129 *)
Example test_x_or_y_91 : x_or_y_spec 91 56 129 129.
Proof.
  unfold x_or_y_spec.
  split.
  - intros Hprime.
    exfalso.
    destruct Hprime as [_ Hrel].
    assert (Hrange: 1 <= 7 < 91) by lia.
    specialize (Hrel 7 Hrange).
    assert (Hgcd: Zis_gcd 7 91 (Z.gcd 7 91)) by apply Zgcd_is_gcd.
    vm_compute in Hgcd.
    pose proof (Zis_gcd_unique _ _ _ _ Hrel Hgcd) as Hcontra.
    destruct Hcontra; discriminate.
  - intros _.
    reflexivity.
Qed.