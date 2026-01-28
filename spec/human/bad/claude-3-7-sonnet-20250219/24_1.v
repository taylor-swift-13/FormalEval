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

Example problem_24_example :
  problem_24_spec 3 1.
Proof.
  unfold problem_24_spec.
  repeat split.
  - (* input mod output = 0 *)
    simpl.
    apply Nat.mod_1_l.
    lia.
  - (* output < input *)
    lia.
  - (* ∀i ∈ (0,3), input mod i=0 → i ≤ output *)
    intros i [Hi_pos Hi_lt] Hmod.
    (* The divisors of 3 less than 3 are only 1 *)
    (* So i must be 1 *)
    assert (i = 1).
    {
      destruct i as [|i'].
      - lia. (* i > 0, so cannot be 0 *)
      - destruct i' as [|i''].
        + reflexivity. (* i = 1 *)
        + (* i = 2 or more, 3 mod 2 ≠ 0, contradicts Hmod *)
          simpl in Hmod.
          discriminate Hmod.
    }
    subst i.
    lia.
Qed.