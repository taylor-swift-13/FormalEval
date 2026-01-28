Require Import Arith.
Require Import Lia.
Require Import Nat.

Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  input mod output = 0 /\
  output < input /\
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Lemma div_mod_500 : forall i, 0 < i -> i < 500 -> 500 mod i = 0 -> i <= 250.
Proof.
  intros i Hi_pos Hi_lt Hi_div.
  destruct (le_gt_dec i 250) as [Hle | Hgt].
  - exact Hle.
  - exfalso.
    assert (Hi_range : 251 <= i <= 499) by lia.
    assert (Hq : 500 / i = 1).
    {
      apply Nat.div_unique with (500 - i).
      - lia.
      - lia.
    }
    assert (Hr : 500 mod i = 500 - i).
    {
      apply Nat.mod_unique with 1.
      - lia.
      - lia.
    }
    rewrite Hr in Hi_div.
    lia.
Qed.

Example problem_24_test : problem_24_spec 500 250.
Proof.
  unfold problem_24_spec.
  split.
  - reflexivity.
  - split.
    + lia.
    + intros i [Hi_pos Hi_lt] Hi_div.
      apply div_mod_500; assumption.
Qed.