Require Import String.
Require Import ZArith.

Open Scope string_scope.
Open Scope Z_scope.

(* Pre: no additional constraints for `strlen` by default *)
Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre "The quick brown fox jumps over the lazy This striThis is aaracter dogM" ->
  exists output, problem_23_spec "The quick brown fox jumps over the lazy This striThis is aaracter dogM" output /\ Z.of_nat output = 70%Z.
Proof.
  intros _.
  exists 70%nat.
  split; [unfold problem_23_spec; simpl; reflexivity | simpl; reflexivity].
Qed.