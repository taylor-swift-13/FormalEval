Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [31; 1; 31], output = 1 *)
Example test_x_or_y_31 : x_or_y_spec 31 1 31 1.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 31 -> 1 = 1 *)
    intros Hprime.
    reflexivity.
  - (* Case: ~ prime 31 -> 1 = 31 *)
    intros Hnot_prime.
    exfalso.
    apply Hnot_prime.
    (* We must prove that 31 is prime to derive a contradiction *)
    apply prime_intro.
    + (* Prove 1 < 31 *)
      lia.
    + (* Prove forall n, 1 <= n < 31 -> rel_prime n 31 *)
      intros n Hrange.
      apply Zgcd_1_rel_prime.
      (* Enumerate all integers between 1 and 31 *)
      assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
              n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/
              n = 21 \/ n = 22 \/ n = 23 \/ n = 24 \/ n = 25 \/ n = 26 \/ n = 27 \/ n = 28 \/ n = 29 \/ n = 30) as Hcases by lia.
      destruct Hcases as [H1 | [H2 | [H3 | [H4 | [H5 | [H6 | [H7 | [H8 | [H9 | [H10 |
                         [H11 | [H12 | [H13 | [H14 | [H15 | [H16 | [H17 | [H18 | [H19 | [H20 |
                         [H21 | [H22 | [H23 | [H24 | [H25 | [H26 | [H27 | [H28 | [H29 | H30]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
        rewrite H1 || rewrite H2 || rewrite H3 || rewrite H4 || rewrite H5 || rewrite H6 ||
        rewrite H7 || rewrite H8 || rewrite H9 || rewrite H10 || rewrite H11 || rewrite H12 ||
        rewrite H13 || rewrite H14 || rewrite H15 || rewrite H16 || rewrite H17 || rewrite H18 ||
        rewrite H19 || rewrite H20 || rewrite H21 || rewrite H22 || rewrite H23 || rewrite H24 ||
        rewrite H25 || rewrite H26 || rewrite H27 || rewrite H28 || rewrite H29 || rewrite H30;
        vm_compute; reflexivity.
Qed.