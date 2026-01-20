Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [2; 2; 0], output = 2 *)
Example test_x_or_y_2 : x_or_y_spec 2 2 0 2.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 2 -> 2 = 2 *)
    intros Hprime.
    reflexivity.
  - (* Case: ~ prime 2 -> 2 = 0 *)
    intros Hnot_prime.
    exfalso.
    apply Hnot_prime.
    (* We must prove that 2 is prime to derive a contradiction *)
    apply prime_intro.
    + (* Prove 1 < 2 *)
      lia.
    + (* Prove forall n, 1 <= n < 2 -> rel_prime n 2 *)
      intros n Hrange.
      apply Zgcd_1_rel_prime.
      (* Enumerate all integers between 1 and 2 *)
      assert (n = 1) as Hcases by lia.
      rewrite Hcases.
      vm_compute; reflexivity.
Qed.