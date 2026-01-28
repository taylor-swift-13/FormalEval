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

Example problem_24_test : problem_24_spec 998 499.
Proof.
  unfold problem_24_spec.
  split.
  - (* 998 mod 499 = 0 *)
    native_compute. reflexivity.
  - split.
    + (* 499 < 998 *)
      lia.
    + (* forall i, 0 < i /\ i < 998 -> 998 mod i = 0 -> i <= 499 *)
      intros i [Hi_pos Hi_lt] Hi_div.
      assert (998 = 2 * 499) as H998 by lia.
      assert (forall d, d > 0 -> 998 mod d = 0 -> exists k, 998 = k * d) as Hdiv_def.
      { intros d Hd_pos Hd_div.
        exists (998 / d).
        rewrite Nat.mul_comm.
        apply Nat.div_exact; lia. }
      destruct (Hdiv_def i Hi_pos Hi_div) as [k Hk].
      assert (k > 0) as Hk_pos by lia.
      assert (k * i = 998) as Hki by lia.
      assert (i <= 499 \/ i > 499) as Hcases by lia.
      destruct Hcases as [Hle | Hgt].
      * exact Hle.
      * assert (k = 1) as Hk1.
        { assert (k >= 2 -> k * i >= 2 * 500) as Hcontra by lia.
          lia. }
        subst k.
        simpl in Hki.
        lia.
Qed.