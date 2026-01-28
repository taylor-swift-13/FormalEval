Require Import String.
Require Import ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre
"off
abcdefgjklmnopqrstuvwxyzfoivife"
  ->
  exists output, problem_23_spec
"off
abcdefgjklmnopqrstuvwxyzfoivife"
 output /\ Z.of_nat output = 35%Z.
Proof.
  intros _.
  exists 35%nat.
  split; [unfold problem_23_spec; vm_compute; reflexivity | vm_compute; reflexivity].
Qed.