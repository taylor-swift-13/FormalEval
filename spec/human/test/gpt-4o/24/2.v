Require Import Arith Lia.

Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  input mod output = 0 /\
  output < input /\
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Example problem_24_example : problem_24_spec 7 1.
Proof.
  unfold problem_24_spec.
  split.
  - simpl. reflexivity.
  - split.
    + lia.
    + intros i [Hi1 Hi2] Hmod.
      assert (Hcases: i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
      destruct Hcases as [H1 | [H2 | [H3 | [H4 | [H5 | H6]]]]].
      * subst. lia.
      * subst. simpl in Hmod. lia.
      * subst. simpl in Hmod. lia.
      * subst. simpl in Hmod. lia.
      * subst. simpl in Hmod. lia.
      * subst. simpl in Hmod. lia.
Qed.