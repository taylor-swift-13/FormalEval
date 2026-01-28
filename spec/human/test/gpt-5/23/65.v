Require Import String.
Require Import ZArith.

Open Scope string_scope.
Open Scope Z_scope.

(* Pre: no additional constraints for `strlen` by default *)
Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre "Hello, WoG1234 This sitriThis is a long string that has many characters in itng h as a 
 newline character5NDKThe quick brown fox jumps over theThe quick brown fox jumps overq the lazy dog lazby Thisthree
four
fiveracter dogQyadEborlod!" ->
  exists output, problem_23_spec "Hello, WoG1234 This sitriThis is a long string that has many characters in itng h as a 
 newline character5NDKThe quick brown fox jumps over theThe quick brown fox jumps overq the lazy dog lazby Thisthree
four
fiveracter dogQyadEborlod!" output /\ Z.of_nat output = 236%Z.
Proof.
  intros _.
  exists 236%nat.
  split; [unfold problem_23_spec; simpl; reflexivity | simpl; reflexivity].
Qed.