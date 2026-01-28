Require Import Arith Lia.

(* Pre: require `input >= 2` so that a largest proper divisor exists *)
Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  (* 1. output 是 input 的一个因数 *)
  input mod output = 0 /\
  (* 2. output 严格小于 input *)
  output < input /\
  (* 3. 对于任何严格小于 input 的正因数 i, i 都小于等于 output *)
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Example test_case_1 : problem_24_spec 3 1.
Proof.
  unfold problem_24_spec.
  split. 
  - (* 3 mod 1 = 0 *)
    simpl. reflexivity.
  - split.
    + (* 1 < 3 *)
      lia.
    + (* ∀i, 0 < i < 3 ∧ 3 mod i = 0 → i ≤ 1 *)
      intros i [Hpos Hlt].
      assert (Hi : i = 1 \/ i = 2) by lia.
      destruct Hi as [Hi | Hi].
      * rewrite Hi. lia.
      * rewrite Hi. 
        intro Hmod.
        simpl in Hmod.
        lia.
Qed.