Require Import Arith Lia.

(* Pre: require `input >= 2` so that a largest proper divisor exists *)
Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  input mod output = 0 /\
  output < input /\
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Example test_case_2 : problem_24_spec 81 27.
Proof.
  unfold problem_24_spec.
  split.
  - simpl. reflexivity.
  - split.
    + lia.
    + intros i [Hpos Hlt].
      assert (Hi : i = 3 \/ i = 9 \/ i = 27 \/ i = 81) by lia.
      destruct Hi as [Hi | [Hi | [Hi | Hi]]].
      * rewrite Hi. lia.
      * rewrite Hi. lia.
      * rewrite Hi. lia.
      * rewrite Hi. lia.
Qed.