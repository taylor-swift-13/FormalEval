Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [17; 9; 17], output = 9 *)
Example test_x_or_y_17 : x_or_y_spec 17 9 17 9.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 17 -> 9 = 9 *)
    intros Hprime.
    reflexivity.
  - (* Case: ~ prime 17 -> 9 = 17 *)
    intros Hnot_prime.
    exfalso.
    apply Hnot_prime.
    (* We must prove that 17 is prime to derive a contradiction *)
    apply prime_intro.
    + (* Prove 1 < 17 *)
      lia.
    + (* Prove forall n, 1 <= n < 17 -> rel_prime n 17 *)
      intros n Hrange.
      apply Zgcd_1_rel_prime.
      (* Enumerate all integers between 1 and 17 *)
      assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16) as Hcases by lia.
      destruct Hcases as [H1 | [H2 | [H3 | [H4 | [H5 | [H6 | [H7 | [H8 | [H9 | [H10 | [H11 | [H12 | [H13 | [H14 | [H15 | H16]]]]]]]]]]]]]]]; 
        rewrite H1 || rewrite H2 || rewrite H3 || rewrite H4 || rewrite H5 || rewrite H6 || rewrite H7 || rewrite H8 || rewrite H9 || rewrite H10 || rewrite H11 || rewrite H12 || rewrite H13 || rewrite H14 || rewrite H15 || rewrite H16;
        vm_compute; reflexivity.
Qed.