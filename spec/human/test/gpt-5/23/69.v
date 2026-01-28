Require Import String.
Require Import ZArith.
Require Import Ascii.

Open Scope string_scope.
Open Scope Z_scope.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre ("thrieeThe quick brown f ox jumps over the lazy dogThe quick brown fox jumps overq the lazy dog" ++ String (Ascii.ascii_of_nat 10) ("four" ++ String (Ascii.ascii_of_nat 10) "five")) ->
  exists output, problem_23_spec ("thrieeThe quick brown f ox jumps over the lazy dogThe quick brown fox jumps overq the lazy dog" ++ String (Ascii.ascii_of_nat 10) ("four" ++ String (Ascii.ascii_of_nat 10) "five")) output /\ Z.of_nat output = 104%Z.
Proof.
  intros _.
  exists (length ("thrieeThe quick brown f ox jumps over the lazy dogThe quick brown fox jumps overq the lazy dog" ++ String (Ascii.ascii_of_nat 10) ("four" ++ String (Ascii.ascii_of_nat 10) "five"))).
  split; [unfold problem_23_spec; reflexivity |].
  vm_compute; reflexivity.
Qed.