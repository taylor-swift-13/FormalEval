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

Example problem_24_test : problem_24_spec 1000 500.
Proof.
  unfold problem_24_spec.
  split.
  - (* 1000 mod 500 = 0 *)
    reflexivity.
  - split.
    + (* 500 < 1000 *)
      lia.
    + (* forall i, 0 < i /\ i < 1000 -> 1000 mod i = 0 -> i <= 500 *)
      intros i [Hi_pos Hi_lt] Hi_div.
      assert (i <= 500 \/ i > 500) as Hi_cases by lia.
      destruct Hi_cases as [Hi_le | Hi_gt].
      * exact Hi_le.
      * assert (Hi_range: 500 < i < 1000) by lia.
        assert (1000 = i * (1000 / i) + 1000 mod i) as Hdiv_eq by (apply Nat.div_mod; lia).
        rewrite Hi_div in Hdiv_eq.
        rewrite Nat.add_0_r in Hdiv_eq.
        assert (1000 / i = 1) as Hquot.
        {
          assert (1000 / i >= 1) as Hge1.
          { apply Nat.div_le_lower_bound; lia. }
          assert (1000 / i < 2) as Hlt2.
          { apply Nat.div_lt_upper_bound; lia. }
          lia.
        }
        rewrite Hquot in Hdiv_eq.
        lia.
Qed.