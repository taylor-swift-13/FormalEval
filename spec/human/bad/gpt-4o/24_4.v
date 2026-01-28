Require Import Arith Lia.

Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  input mod output = 0 /\
  output < input /\
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Example problem_24_example : problem_24_spec 100 50.
Proof.
  unfold problem_24_spec.
  split.
  - simpl. reflexivity.
  - split.
    + lia.
    + intros i [Hi1 Hi2] Hmod.
      destruct (Nat.eq_dec i 50).
      * subst. lia.
      * assert (Hle: i <= 50) by (apply (Nat.div_le_upper_bound 100 i); lia).
        lia.
Qed.