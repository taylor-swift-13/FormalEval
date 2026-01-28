Require Import String.
Require Import ZArith.

Open Scope string_scope.
Open Scope Z_scope.

(* Pre: no additional constraints for `strlen` by default *)
Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre "1234 This sitriThis is a long string that has many characters in itng has a 
 neThe quick brown f ox jumps over the lazygwline character5" ->
  exists output, problem_23_spec "1234 This sitriThis is a long string that has many characters in itng has a 
 neThe quick brown f ox jumps over the lazygwline character5" output /\ Z.of_nat output = 137%Z.
Proof.
  intros _.
  exists (length "1234 This sitriThis is a long string that has many characters in itng has a 
 neThe quick brown f ox jumps over the lazygwline character5").
  split; [unfold problem_23_spec; reflexivity | vm_compute; reflexivity].
Qed.