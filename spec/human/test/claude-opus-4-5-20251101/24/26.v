Require Import Arith.
Require Import Lia.

Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  input mod output = 0 /\
  output < input /\
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Lemma mod_82_41 : 82 mod 41 = 0.
Proof.
  reflexivity.
Qed.

Lemma mod_82_check : forall i, 41 < i < 82 -> 82 mod i <> 0.
Proof.
  intros i [Hi_gt Hi_lt].
  assert (i = 42 \/ i = 43 \/ i = 44 \/ i = 45 \/ i = 46 \/ i = 47 \/ i = 48 \/ i = 49 \/ 
          i = 50 \/ i = 51 \/ i = 52 \/ i = 53 \/ i = 54 \/ i = 55 \/ i = 56 \/ i = 57 \/ 
          i = 58 \/ i = 59 \/ i = 60 \/ i = 61 \/ i = 62 \/ i = 63 \/ i = 64 \/ i = 65 \/ 
          i = 66 \/ i = 67 \/ i = 68 \/ i = 69 \/ i = 70 \/ i = 71 \/ i = 72 \/ i = 73 \/ 
          i = 74 \/ i = 75 \/ i = 76 \/ i = 77 \/ i = 78 \/ i = 79 \/ i = 80 \/ i = 81) as Hi_cases by lia.
  destruct Hi_cases as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
  subst i; simpl; discriminate.
Qed.

Example problem_24_test : problem_24_spec 82 41.
Proof.
  unfold problem_24_spec.
  split.
  - exact mod_82_41.
  - split.
    + lia.
    + intros i [Hi_pos Hi_lt] Hi_div.
      destruct (Nat.le_gt_cases i 41) as [H_le | H_gt].
      * exact H_le.
      * exfalso.
        apply mod_82_check in Hi_div.
        -- exact Hi_div.
        -- lia.
Qed.