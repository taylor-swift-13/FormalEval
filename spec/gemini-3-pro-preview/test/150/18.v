Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [31; -5; 22], output = -5 *)
Example test_x_or_y_31 : x_or_y_spec 31 (-5) 22 (-5).
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 31 -> -5 = -5 *)
    intros Hprime.
    reflexivity.
  - (* Case: ~ prime 31 -> -5 = 22 *)
    intros Hnot_prime.
    exfalso.
    apply Hnot_prime.
    apply prime_intro.
    + lia.
    + intros n Hrange.
      apply Zgcd_1_rel_prime.
      assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
              n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/
              n = 21 \/ n = 22 \/ n = 23 \/ n = 24 \/ n = 25 \/ n = 26 \/ n = 27 \/ n = 28 \/ n = 29 \/ n = 30) as Hcases by lia.
      repeat (destruct Hcases as [Hcases | Hcases]; [ rewrite Hcases; vm_compute; reflexivity | ]).
      rewrite Hcases; vm_compute; reflexivity.
Qed.