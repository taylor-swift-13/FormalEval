Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [62; 49; 100], output = 100 *)
Example test_x_or_y_62 : x_or_y_spec 62 49 100 100.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 62 -> 100 = 49 *)
    intros Hprime.
    exfalso.
    (* We must prove that 62 is not prime to derive a contradiction *)
    (* 62 is divisible by 2, so it cannot be prime *)
    destruct Hprime as [_ Hrel].
    assert (Hrange : 1 <= 2 < 62) by lia.
    specialize (Hrel 2 Hrange).
    (* rel_prime 2 62 implies gcd(2, 62) = 1 *)
    apply Zgcd_1_rel_prime in Hrel.
    vm_compute in Hrel.
    discriminate.
  - (* Case: ~ prime 62 -> 100 = 100 *)
    intros _.
    reflexivity.
Qed.