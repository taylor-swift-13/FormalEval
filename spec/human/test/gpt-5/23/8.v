Require Import String.
Require Import ZArith.

Open Scope string_scope.
Open Scope Z_scope.

(* Pre: no additional constraints for `strlen` by default *)
Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre "abcdefghijklmnopqrstuvwxyz" ->
  exists output, problem_23_spec "abcdefghijklmnopqrstuvwxyz" output /\ Z.of_nat output = 26%Z.
Proof.
  intros _.
  exists 26%nat.
  split; [unfold problem_23_spec; simpl; reflexivity | simpl; reflexivity].
Qed.