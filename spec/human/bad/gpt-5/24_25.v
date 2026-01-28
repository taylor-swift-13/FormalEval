Require Import PeanoNat.
Require Import Lia.

Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  input mod output = 0 /\
  output < input /\
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Example problem_24_example_236_118 : problem_24_pre 236 /\ problem_24_spec 236 118.
Proof.
  split.
  - unfold problem_24_pre. lia.
  - unfold problem_24_spec.
    split.
    + change (236 mod 118) with ((118 * 2) mod 118). rewrite Nat.mod_mul. reflexivity.
    + split.
      * lia.
      * intros i [Hi_pos Hi_lt] Hi_div.
        apply Nat.mod_divides in Hi_div; [| lia].
        destruct Hi_div as [k Hk].
        destruct k as [|k'].
        -- rewrite Hk. lia.
        -- destruct k' as [|k''].
           ++ rewrite Hk in Hi_lt. lia.
           ++ assert (2 <= S (S k'')) by lia.
              assert (i * 2 <= i * S (S k'')) by (apply Nat.mul_le_mono_pos_l; [lia|assumption]).
              rewrite Hk in H.
              lia.
Qed.