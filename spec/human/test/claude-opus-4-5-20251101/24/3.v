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

Example problem_24_test : problem_24_spec 10 5.
Proof.
  unfold problem_24_spec.
  split.
  - simpl. reflexivity.
  - split.
    + lia.
    + intros i [Hi_pos Hi_lt] Hi_div.
      assert (i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9) as Hi_cases by lia.
      destruct Hi_cases as [Hi_eq1 | [Hi_eq2 | [Hi_eq3 | [Hi_eq4 | [Hi_eq5 | [Hi_eq6 | [Hi_eq7 | [Hi_eq8 | Hi_eq9]]]]]]]].
      * lia.
      * lia.
      * subst i. simpl in Hi_div. discriminate.
      * subst i. simpl in Hi_div. discriminate.
      * lia.
      * subst i. simpl in Hi_div. discriminate.
      * subst i. simpl in Hi_div. discriminate.
      * subst i. simpl in Hi_div. discriminate.
      * subst i. simpl in Hi_div. discriminate.
Qed.