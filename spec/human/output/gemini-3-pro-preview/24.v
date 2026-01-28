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

Example test_case_24 : problem_24_spec 3 1.
Proof.
  unfold problem_24_spec.
  (* Use explicit split instead of repeat split to ensure goal control *)
  split.
  - (* Goal 1: 3 mod 1 = 0 *)
    simpl. reflexivity.
  - split.
    + (* Goal 2: 1 < 3 *)
      lia.
    + (* Goal 3: forall i, 0 < i < 3 -> 3 mod i = 0 -> i <= 1 *)
      intros i [Hgt0 Hlt3] Hdiv.
      (* Since 0 < i < 3, i can only be 1 or 2 *)
      assert (i = 1 \/ i = 2) as Hcases by lia.
      destruct Hcases as [H1 | H2].
      * (* Case i = 1 *)
        subst.
        lia. (* 1 <= 1 holds *)
      * (* Case i = 2 *)
        subst.
        (* 3 mod 2 evaluates to 1, so hypothesis Hdiv becomes 1 = 0 *)
        simpl in Hdiv.
        discriminate Hdiv.
Qed.