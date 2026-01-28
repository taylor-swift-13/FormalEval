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

Example problem_24_test : problem_24_spec 3 1.
Proof.
  unfold problem_24_spec.
  split.
  - (* 3 mod 1 = 0 *)
    simpl. reflexivity.
  - split.
    + (* 1 < 3 *)
      lia.
    + (* forall i, 0 < i /\ i < 3 -> 3 mod i = 0 -> i <= 1 *)
      intros i [Hi_pos Hi_lt] Hi_div.
      (* i can only be 1 or 2 since 0 < i < 3 *)
      assert (i = 1 \/ i = 2) as Hi_cases by lia.
      destruct Hi_cases as [Hi_eq1 | Hi_eq2].
      * (* i = 1 *)
        lia.
      * (* i = 2 *)
        subst i.
        simpl in Hi_div.
        discriminate.
Qed.