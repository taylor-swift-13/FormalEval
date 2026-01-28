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

Example test_case_24_new : problem_24_spec 4 2.
Proof.
  unfold problem_24_spec.
  split.
  - (* Goal 1: 4 mod 2 = 0 *)
    simpl. reflexivity.
  - split.
    + (* Goal 2: 2 < 4 *)
      lia.
    + (* Goal 3: forall i, 0 < i < 4 -> 4 mod i = 0 -> i <= 2 *)
      intros i [Hgt0 Hlt4] Hdiv.
      (* Since 0 < i < 4, i can be 1, 2, or 3 *)
      assert (i = 1 \/ i = 2 \/ i = 3) as Hcases by lia.
      destruct Hcases as [H1 | [H2 | H3]].
      * (* Case i = 1 *)
        subst. lia.
      * (* Case i = 2 *)
        subst. lia.
      * (* Case i = 3 *)
        subst.
        simpl in Hdiv.
        discriminate Hdiv.
Qed.