Require Import String.
Require Import Ascii.
Require Import ZArith.

Open Scope string_scope.
Open Scope Z_scope.

(* Pre: no additional constraints for `strlen` by default *)
Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example problem_23_test_case:
  problem_23_pre ("one" ++ String (Ascii.ascii_of_nat 10)
    ("twot" ++ String (Ascii.ascii_of_nat 10)
      ("thrThis is a long string that has  many characterns in itee" ++ String (Ascii.ascii_of_nat 10)
        ("four" ++ String (Ascii.ascii_of_nat 10) "five")))) ->
  exists output,
    problem_23_spec ("one" ++ String (Ascii.ascii_of_nat 10)
      ("twot" ++ String (Ascii.ascii_of_nat 10)
        ("thrThis is a long string that has  many characterns in itee" ++ String (Ascii.ascii_of_nat 10)
          ("four" ++ String (Ascii.ascii_of_nat 10) "five")))) output /\
    Z.of_nat output = 78%Z.
Proof.
  intros _.
  exists 78%nat.
  split; [unfold problem_23_spec; simpl; reflexivity | simpl; reflexivity].
Qed.