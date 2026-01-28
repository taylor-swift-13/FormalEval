Require Import String.
Require Import ZArith.

Open Scope string_scope.
Open Scope Z_scope.

(* Pre: no additional constraints for `strlen` by default *)
Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre "abcdefgjklmnopqrstuvwxyzive" ->
  exists output, problem_23_spec "abcdefgjklmnopqrstuvwxyzive" output /\ Z.of_nat output = 27%Z.
Proof.
  intros _.
  exists 27%nat.
  split; [unfold problem_23_spec; simpl; reflexivity | simpl; reflexivity].
Qed.