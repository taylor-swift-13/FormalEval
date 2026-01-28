Require Import Arith.
Require Import Lia.

(* Pre: require `input >= 2` so that a largest proper divisor exists *)
Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  (* 1. output is a divisor of input *)
  input mod output = 0 /\

  (* 2. output is strictly less than input *)
  output < input /\

  (* 3. for any divisor i strictly less than input, i <= output *)
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Example test_case_24 : problem_24_spec 10 5.
Proof.
  unfold problem_24_spec.
  split.
  - (* Goal 1: 10 mod 5 = 0 *)
    simpl. reflexivity.
  - split.
    + (* Goal 2: 5 < 10 *)
      lia.
    + (* Goal 3: forall i, 0 < i < 10 -> 10 mod i = 0 -> i <= 5 *)
      intros i [Hgt0 Hlt10] Hdiv.
      (* Split cases based on whether i <= 5 or i > 5 *)
      assert (i <= 5 \/ 5 < i) as [Hle | Hgt] by lia.
      * (* Case i <= 5 *)
        assumption.
      * (* Case i > 5. Since i < 10, i can be 6, 7, 8, 9 *)
        assert (i = 6 \/ i = 7 \/ i = 8 \/ i = 9) as Hcases by lia.
        destruct Hcases as [H | [H | [H | H]]]; subst; simpl in Hdiv; discriminate.
Qed.