Require Import Arith Lia.

Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  input mod output = 0 /\
  output < input /\
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Example problem_24_example : problem_24_spec 235 47.
Proof.
  unfold problem_24_spec.
  split.
  - simpl. reflexivity.
  - split.
    + lia.
    + intros i [Hi1 Hi2] Hmod.
      assert (Hdiv: 235 = 5 * 47) by reflexivity.
      assert (Hcases: i = 1 \/ i = 5 \/ i = 47 \/ i = 235) by lia.
      destruct Hcases as [H1 | [H5 | [H47 | H235]]].
      * subst. lia.
      * subst. simpl in Hmod. lia.
      * subst. lia.
      * subst. lia.
Qed.