Require Import Arith.
Require Import ZArith.
Require Import Coq.ZArith.Znumtheory.

Definition problem_150_spec (n x y res : nat) : Prop :=
  (prime (Z.of_nat n) -> res = x) /\
  (~ prime (Z.of_nat n) -> res = y).

Example test_case_7_34_12 : problem_150_spec 7 34 12 34.
Proof.
  unfold problem_150_spec.
  split.
  - (* prime (Z.of_nat 7) -> res = x *)
    intro H.
    reflexivity.
  - (* ~ prime (Z.of_nat 7) -> res = y *)
    intro H.
    (* We need to show that 7 is prime to get a contradiction *)
    assert (prime_7: prime 7%Z).
    { 
      apply prime_intro.
      + unfold gt. lia.
      + intros m Hdiv.
        assert (Hrange: 1 < m < 7 \/ m = 7).
        { 
          apply Z.divisors_up_to_n; try lia.
          exists 1%Z. lia.
        }
        destruct Hrange as [Hrange|Heq].
        * destruct Hrange as [Hlt1 Hlt2].
          apply Z.divide_pos_bound in Hdiv; try lia.
          destruct Hdiv as [Hdiv1 Hdiv2].
          assert (Hdivisors: m = 2 \/ m = 3 \/ m = 4 \/ m = 5 \/ m = 6).
          { lia. }
          destruct Hdivisors as [Hm|Hm].
          + rewrite Hm in Hdiv.
            apply Z.divide_1_r in Hdiv.
            lia.
          + destruct Hm as [Hm|Hm].
            * rewrite Hm in Hdiv.
              apply Z.divide_1_r in Hdiv.
              lia.
            * destruct Hm as [Hm|Hm].
              rewrite Hm in Hdiv.
              apply Z.divide_1_r in Hdiv.
              lia.
              destruct Hm as [Hm|Hm].
              rewrite Hm in Hdiv.
              apply Z.divide_1_r in Hdiv.
              lia.
              rewrite Hm in Hdiv.
              apply Z.divide_1_r in Hdiv.
              lia.
        * rewrite Heq.
          apply Z.divide_refl.
    }
    (* Now we have a contradiction with H: ~ prime (Z.of_nat 7) *)
    assert (Hconv: Z.of_nat 7 = 7%Z) by reflexivity.
    rewrite Hconv in H.
    contradiction H.
Qed.