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

Example problem_24_test : problem_24_spec 100 50.
Proof.
  unfold problem_24_spec.
  split.
  - simpl. reflexivity.
  - split.
    + lia.
    + intros i [Hi_pos Hi_lt] Hi_div.
      assert (i <= 50 \/ i > 50) as Hi_cases by lia.
      destruct Hi_cases as [Hi_le50 | Hi_gt50].
      * exact Hi_le50.
      * assert (i = 51 \/ i = 52 \/ i = 53 \/ i = 54 \/ i = 55 \/ i = 56 \/ i = 57 \/ i = 58 \/ i = 59 \/ i = 60 \/ i = 61 \/ i = 62 \/ i = 63 \/ i = 64 \/ i = 65 \/ i = 66 \/ i = 67 \/ i = 68 \/ i = 69 \/ i = 70 \/ i = 71 \/ i = 72 \/ i = 73 \/ i = 74 \/ i = 75 \/ i = 76 \/ i = 77 \/ i = 78 \/ i = 79 \/ i = 80 \/ i = 81 \/ i = 82 \/ i = 83 \/ i = 84 \/ i = 85 \/ i = 86 \/ i = 87 \/ i = 88 \/ i = 89 \/ i = 90 \/ i = 91 \/ i = 92 \/ i = 93 \/ i = 94 \/ i = 95 \/ i = 96 \/ i = 97 \/ i = 98 \/ i = 99) as Hi_range by lia.
        destruct Hi_range as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
        subst i; simpl in Hi_div; discriminate.
Qed.