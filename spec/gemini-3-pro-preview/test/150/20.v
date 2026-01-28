Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [61; 20; 40], output = 20 *)
Example test_x_or_y_61 : x_or_y_spec 61 20 40 20.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 61 -> 20 = 20 *)
    intros Hprime.
    reflexivity.
  - (* Case: ~ prime 61 -> 20 = 40 *)
    intros Hnot_prime.
    exfalso.
    apply Hnot_prime.
    (* We must prove that 61 is prime to derive a contradiction *)
    apply prime_intro.
    + (* Prove 1 < 61 *)
      lia.
    + (* Prove forall n, 1 <= n < 61 -> rel_prime n 61 *)
      intros n Hrange.
      apply Zgcd_1_rel_prime.
      (* Enumerate all integers between 1 and 61 *)
      assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
              n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/
              n = 21 \/ n = 22 \/ n = 23 \/ n = 24 \/ n = 25 \/ n = 26 \/ n = 27 \/ n = 28 \/ n = 29 \/ n = 30 \/
              n = 31 \/ n = 32 \/ n = 33 \/ n = 34 \/ n = 35 \/ n = 36 \/ n = 37 \/ n = 38 \/ n = 39 \/ n = 40 \/
              n = 41 \/ n = 42 \/ n = 43 \/ n = 44 \/ n = 45 \/ n = 46 \/ n = 47 \/ n = 48 \/ n = 49 \/ n = 50 \/
              n = 51 \/ n = 52 \/ n = 53 \/ n = 54 \/ n = 55 \/ n = 56 \/ n = 57 \/ n = 58 \/ n = 59 \/ n = 60) as Hcases by lia.
      repeat (destruct Hcases as [Hcases | Hcases]; [subst; vm_compute; reflexivity | ]).
      subst; vm_compute; reflexivity.
Qed.