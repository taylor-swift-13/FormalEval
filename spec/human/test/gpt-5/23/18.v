Require Import String.
Require Import ZArith.

Open Scope string_scope.
Open Scope Z_scope.

(* Pre: no additional constraints for `strlen` by default *)
Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre " This striThis is a long string that has many characters in itng has a 
 newline character" ->
  exists output, problem_23_spec " This striThis is a long string that has many characters in itng has a 
 newline character" output /\ Z.of_nat output = 90%Z.
Proof.
  intros _.
  exists 90%nat.
  split; [unfold problem_23_spec; simpl; reflexivity | simpl; reflexivity].
Qed.