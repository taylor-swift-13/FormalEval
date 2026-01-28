Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [6; 123; 100], output = 100 *)
Example test_x_or_y_6 : x_or_y_spec 6 123 100 100.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 6 -> 100 = 123 *)
    intros Hprime.
    exfalso.
    destruct Hprime as [_ Hrel].
    (* Since 6 is prime, it must be relatively prime to 2 (as 1 <= 2 < 6) *)
    assert (Hcoprime: rel_prime 2 6).
    { apply Hrel. lia. }
    (* However, gcd(2, 6) = 2, which contradicts rel_prime 2 6 *)
    apply Zgcd_1_rel_prime in Hcoprime.
    vm_compute in Hcoprime.
    discriminate.
  - (* Case: ~ prime 6 -> 100 = 100 *)
    intros _.
    reflexivity.
Qed.