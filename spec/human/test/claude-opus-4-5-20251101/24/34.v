Require Import Arith.
Require Import Lia.

(* Pre: require `input >= 2` so that a largest proper divisor exists *)
Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  (* 1. output 是 input 的一个因数 *)
  input mod output = 0 /\

  (* 2. output 严格小于 input *)
  output < input /\

  (* 3. 对于任何严格小于 input 的正因数 i, i 都小于等于 output *)
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Example problem_24_test : problem_24_spec 238 119.
Proof.
  unfold problem_24_spec.
  split.
  - (* 238 mod 119 = 0 *)
    reflexivity.
  - split.
    + (* 119 < 238 *)
      lia.
    + (* forall i, 0 < i /\ i < 238 -> 238 mod i = 0 -> i <= 119 *)
      intros i [Hi_pos Hi_lt] Hi_div.
      assert (238 = 2 * 119) as H238 by lia.
      assert (i = 1 \/ i = 2 \/ i = 7 \/ i = 14 \/ i = 17 \/ i = 34 \/ i = 119 \/ (i <> 1 /\ i <> 2 /\ i <> 7 /\ i <> 14 /\ i <> 17 /\ i <> 34 /\ i <> 119)) as Hi_cases by lia.
      destruct Hi_cases as [H1 | [H2 | [H7 | [H14 | [H17 | [H34 | [H119 | Hother]]]]]]].
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * lia.
      * destruct (Nat.eq_dec (238 mod i) 0) as [Hdiv | Hndiv].
        -- assert (i <= 119 \/ i > 119) as Hcmp by lia.
           destruct Hcmp as [Hle | Hgt].
           ++ lia.
           ++ assert (238 = i * (238 / i) + 238 mod i) as Hdiv_eq by (apply Nat.div_mod; lia).
              rewrite Hdiv in Hdiv_eq.
              rewrite Nat.add_0_r in Hdiv_eq.
              assert (238 / i = 0 \/ 238 / i = 1 \/ 238 / i >= 2) as Hq by lia.
              destruct Hq as [Hq0 | [Hq1 | Hq2]].
              ** rewrite Hq0 in Hdiv_eq. lia.
              ** rewrite Hq1 in Hdiv_eq. lia.
              ** assert (i * (238 / i) >= i * 2) by lia. lia.
        -- rewrite Hi_div in Hndiv. lia.
Qed.