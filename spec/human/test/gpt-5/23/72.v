Require Import String.
Require Import ZArith.
Require Import Ascii.

Open Scope string_scope.
Open Scope Z_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre ("off" ++ String.String (Ascii.ascii_of_nat 10) "foivife") ->
  exists output, problem_23_spec ("off" ++ String.String (Ascii.ascii_of_nat 10) "foivife") output /\ Z.of_nat output = 11%Z.
Proof.
  intros _.
  exists 11%nat.
  split; [unfold problem_23_spec; simpl; reflexivity | simpl; reflexivity].
Qed.