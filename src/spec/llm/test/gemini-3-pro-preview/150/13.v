Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [11; 1; 0], output = 1 *)
Example test_x_or_y_11 : x_or_y_spec 11 1 0 1.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 11 -> 1 = 1 *)
    intros Hprime.
    reflexivity.
  - (* Case: ~ prime 11 -> 1 = 0 *)
    intros Hnot_prime.
    exfalso.
    apply Hnot_prime.
    (* We must prove that 11 is prime to derive a contradiction *)
    apply prime_intro.
    + (* Prove 1 < 11 *)
      lia.
    + (* Prove forall n, 1 <= n < 11 -> rel_prime n 11 *)
      intros n Hrange.
      apply Zgcd_1_rel_prime.
      (* Enumerate all integers between 1 and 11 *)
      assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10) as Hcases by lia.
      destruct Hcases as [H1 | [H2 | [H3 | [H4 | [H5 | [H6 | [H7 | [H8 | [H9 | H10]]]]]]]]]; 
        rewrite H1 || rewrite H2 || rewrite H3 || rewrite H4 || rewrite H5 || rewrite H6 || rewrite H7 || rewrite H8 || rewrite H9 || rewrite H10;
        vm_compute; reflexivity.
Qed.