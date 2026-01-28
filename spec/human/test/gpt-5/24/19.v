Require Import Arith.
Require Import Lia.

Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  input mod output = 0 /\
  output < input /\
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Example problem_24_example_998_499 : problem_24_pre 998 /\ problem_24_spec 998 499.
Proof.
  split.
  - unfold problem_24_pre. lia.
  - unfold problem_24_spec.
    split.
    + vm_compute. reflexivity.
    + split.
      * lia.
      * intros i [Hi_pos Hi_lt] Hi_div.
        destruct i as [|i'].
        -- lia.
        -- apply Nat.mod_divides in Hi_div; [| lia].
           destruct Hi_div as [k Hk].
           destruct k as [|k'].
           ++ simpl in Hk. lia.
           ++ destruct k' as [|k''].
              ** simpl in Hk. subst. lia.
              ** assert (Hle : (S i') * 2 <= (S i') * (S (S k''))).
                 { apply Nat.mul_le_mono_pos_l; lia. }
                 rewrite <- Hk in Hle.
                 rewrite Nat.mul_comm in Hle.
                 lia.
Qed.