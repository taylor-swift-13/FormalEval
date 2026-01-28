Require Import Arith Lia.

(* Pre: require `input >= 2` so that a largest proper divisor exists *)
Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  input mod output = 0 /\
  output < input /\
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Example test_case_1 : problem_24_spec 100 50.
Proof.
  unfold problem_24_spec.
  split.
  - (* 100 mod 50 = 0 *)
    simpl. reflexivity.
  - split.
    + (* 50 < 100 *)
      lia.
    + (* ∀i, 0 < i < 100 ∧ 100 mod i = 0 → i ≤ 50 *)
      intros i [Hpos Hlt].
      assert (i_divisors_100 : 100 mod i = 0) by (exact Hlt).
      assert (i = 50 \/ i = 25 \/ i = 20 \/ i = 10 \/ i = 5 \/ i = 4 \/ i = 2 \/ i = 1) by lia.
      destruct H as [Hi | [Hi | [Hi | [Hi | [Hi | [Hi | [Hi | Hi]]]]]]].
      * rewrite Hi. lia.
      * rewrite Hi. lia.
      * rewrite Hi. lia.
      * rewrite Hi. lia.
      * rewrite Hi. lia.
      * rewrite Hi. lia.
      * rewrite Hi. lia.
      * rewrite Hi. lia.
Qed.