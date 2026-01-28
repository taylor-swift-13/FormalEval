Require Import Arith Lia.

(* Pre: require `input >= 2` so that a largest proper divisor exists *)
Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  (* 1. output is a divisor of input *)
  input mod output = 0 /\

  (* 2. output is strictly less than input *)
  output < input /\

  (* 3. for any divisor i of input that is strictly less than input, i is less than or equal to output *)
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Example problem_24_example : problem_24_spec 3 1.
Proof.
  unfold problem_24_spec.
  split.
  - simpl. reflexivity.
  - split.
    + lia.
    + intros i [Hi1 Hi2] Hmod.
      assert (Hcases: i = 1 \/ i = 2) by lia.
      destruct Hcases as [H1 | H2].
      * subst. lia.
      * subst. simpl in Hmod. lia.
Qed.