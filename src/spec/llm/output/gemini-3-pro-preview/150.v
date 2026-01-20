Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [7; 34; 12], output = 34 *)
Example test_x_or_y_7 : x_or_y_spec 7 34 12 34.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 7 -> 34 = 34 *)
    intros Hprime.
    reflexivity.
  - (* Case: ~ prime 7 -> 34 = 12 *)
    intros Hnot_prime.
    exfalso.
    apply Hnot_prime.
    (* We must prove that 7 is prime to derive a contradiction *)
    apply prime_intro.
    + (* Prove 1 < 7 *)
      lia.
    + (* Prove forall n, 1 <= n < 7 -> rel_prime n 7 *)
      intros n Hrange.
      apply Zgcd_1_rel_prime.
      (* Enumerate all integers between 1 and 7 *)
      assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6) as Hcases by lia.
      destruct Hcases as [H1 | [H2 | [H3 | [H4 | [H5 | H6]]]]]; 
        rewrite H1 || rewrite H2 || rewrite H3 || rewrite H4 || rewrite H5 || rewrite H6;
        vm_compute; reflexivity.
Qed.