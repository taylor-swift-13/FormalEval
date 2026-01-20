Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [3; 33; 5212], output = 33 *)
Example test_x_or_y_3 : x_or_y_spec 3 33 5212 33.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 3 -> 33 = 33 *)
    intros Hprime.
    reflexivity.
  - (* Case: ~ prime 3 -> 33 = 5212 *)
    intros Hnot_prime.
    exfalso.
    apply Hnot_prime.
    (* We must prove that 3 is prime to derive a contradiction *)
    apply prime_intro.
    + (* Prove 1 < 3 *)
      lia.
    + (* Prove forall n, 1 <= n < 3 -> rel_prime n 3 *)
      intros n Hrange.
      apply Zgcd_1_rel_prime.
      (* Enumerate all integers between 1 and 3 *)
      assert (n = 1 \/ n = 2) as Hcases by lia.
      destruct Hcases as [H1 | H2]; 
        rewrite H1 || rewrite H2;
        vm_compute; reflexivity.
Qed.