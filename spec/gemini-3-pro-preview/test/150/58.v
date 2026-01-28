Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [5; 101; 5], output = 101 *)
Example test_x_or_y_5 : x_or_y_spec 5 101 5 101.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 5 -> 101 = 101 *)
    intros Hprime.
    reflexivity.
  - (* Case: ~ prime 5 -> 101 = 5 *)
    intros Hnot_prime.
    exfalso.
    apply Hnot_prime.
    (* We must prove that 5 is prime to derive a contradiction *)
    apply prime_intro.
    + (* Prove 1 < 5 *)
      lia.
    + (* Prove forall n, 1 <= n < 5 -> rel_prime n 5 *)
      intros n Hrange.
      apply Zgcd_1_rel_prime.
      (* Enumerate all integers between 1 and 5 *)
      assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4) as Hcases by lia.
      destruct Hcases as [H1 | [H2 | [H3 | H4]]]; 
        rewrite H1 || rewrite H2 || rewrite H3 || rewrite H4;
        vm_compute; reflexivity.
Qed.