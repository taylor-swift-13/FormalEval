Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Open Scope Z_scope.

(* Specification definition *)
Definition x_or_y_spec (n x y res : Z) : Prop :=
  (prime n -> res = x) /\
  (~ prime n -> res = y).

(* Test case: input = [17; 18; 9], output = 18 *)
Example test_x_or_y_17 : x_or_y_spec 17 18 9 18.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: prime 17 -> 18 = 18 *)
    intros Hprime.
    reflexivity.
  - (* Case: ~ prime 17 -> 18 = 9 *)
    intros Hnot_prime.
    exfalso.
    apply Hnot_prime.
    apply prime_intro.
    + lia.
    + intros n Hrange.
      apply Zgcd_1_rel_prime.
      assert (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ 
              n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16) as Hcases by lia.
      destruct Hcases as [H1 | [H2 | [H3 | [H4 | [H5 | [H6 | [H7 | [H8 | [H9 | [H10 | [H11 | [H12 | [H13 | [H14 | [H15 | H16]]]]]]]]]]]]]]];
      subst; vm_compute; reflexivity.
Qed.