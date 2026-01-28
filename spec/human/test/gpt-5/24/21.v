Require Import Arith.
Require Import Lia.

(* Pre: require `input >= 2` so that a largest proper divisor exists *)
Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  input mod output = 0 /\
  output < input /\
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Example problem_24_example_22_11 : problem_24_pre 22 /\ problem_24_spec 22 11.
Proof.
  split.
  - unfold problem_24_pre. lia.
  - unfold problem_24_spec.
    split.
    + simpl. reflexivity.
    + split.
      * lia.
      * intros i [Hi_pos Hi_lt] Hi_div.
        apply Nat.mod_divides in Hi_div; [| lia ].
        destruct Hi_div as [q Hq].
        destruct q as [|q'].
        -- simpl in Hq. lia.
        -- destruct q' as [|q''].
           ++ simpl in Hq. subst. lia.
           ++ rewrite Nat.mul_succ_r in Hq.
              rewrite Nat.mul_succ_r in Hq.
              assert (i + i <= 22)%nat.
              { rewrite Hq. lia. }
              lia.
Qed.