Require Import String.
Require Import ZArith.

Open Scope string_scope.
Open Scope Z_scope.

(* Pre: no additional constraints for `strlen` by default *)
Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre "abcdefghijklmnopq1234 This striThis is a long string that has many characters in itng has a 
 newline character5rstuvwxyz" ->
  exists output, problem_23_spec "abcdefghijklmnopq1234 This striThis is a long string that has many characters in itng has a 
 newline character5rstuvwxyz" output /\ Z.of_nat output = 121%Z.
Proof.
  intros _.
  exists (length "abcdefghijklmnopq1234 This striThis is a long string that has many characters in itng has a 
 newline character5rstuvwxyz").
  split; [unfold problem_23_spec; reflexivity | simpl; reflexivity].
Qed.