Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [41; 122; 455], output = 122 *)
Example test_x_or_y_41 : x_or_y_spec 41 122 455 122.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 41 -> 122 = 122 *)
    intros Hprime.
    reflexivity.
  - (* Case: ~ prime 41 -> 122 = 455 *)
    intros Hnot_prime.
    exfalso.
    apply Hnot_prime.
    (* We must prove that 41 is prime to derive a contradiction *)
    apply prime_intro.
    + (* Prove 1 < 41 *)
      lia.
    + (* Prove forall n, 1 <= n < 41 -> rel_prime n 41 *)
      intros n Hrange.
      apply Zgcd_1_rel_prime.
      (* Enumerate all integers between 1 and 41 *)
      assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ 
              n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/ 
              n = 21 \/ n = 22 \/ n = 23 \/ n = 24 \/ n = 25 \/ n = 26 \/ n = 27 \/ n = 28 \/ n = 29 \/ n = 30 \/ 
              n = 31 \/ n = 32 \/ n = 33 \/ n = 34 \/ n = 35 \/ n = 36 \/ n = 37 \/ n = 38 \/ n = 39 \/ n = 40) 
              as Hcases by lia.
      repeat match goal with | [ H : _ \/ _ |- _ ] => destruct H end;
        subst; vm_compute; reflexivity.
Qed.