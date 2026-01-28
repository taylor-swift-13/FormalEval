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

Example problem_24_test : problem_24_spec 36 18.
Proof.
  unfold problem_24_spec.
  split.
  - simpl. reflexivity.
  - split.
    + lia.
    + intros i [Hi_pos Hi_lt] Hi_div.
      assert (i <= 18 \/ i > 18) as Hi_cases by lia.
      destruct Hi_cases as [Hi_le18 | Hi_gt18].
      * exact Hi_le18.
      * assert (i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/ i = 30 \/ i = 31 \/ i = 32 \/ i = 33 \/ i = 34 \/ i = 35) as Hi_vals by lia.
        destruct Hi_vals as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]];
        subst i; simpl in Hi_div; discriminate.
Qed.