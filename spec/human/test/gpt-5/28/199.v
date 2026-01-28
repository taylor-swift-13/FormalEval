Require Import List String.
Require Import Ascii.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec
  [
    String.append "hello"%string (String.String (Ascii.ascii_of_nat 10) "world"%string);
    String.append
      (String.append
        (String.append
          (String.append "this"%string (String.String (Ascii.ascii_of_nat 10) "string"%string))
          (String.String (Ascii.ascii_of_nat 10) "has"%string))
        (String.String (Ascii.ascii_of_nat 10) "multiple"%string))
      (String.String (Ascii.ascii_of_nat 10) "newlines"%string);
    "jumps"%string;
    String.append
      (String.append
        (String.append
          (String.append "this"%string (String.String (Ascii.ascii_of_nat 10) "string"%string))
          (String.String (Ascii.ascii_of_nat 10) "has"%string))
        (String.String (Ascii.ascii_of_nat 10) "multipule"%string))
      (String.String (Ascii.ascii_of_nat 10) "newlines"%string);
    String.append "hello"%string (String.String (Ascii.ascii_of_nat 10) "world"%string);
    String.append
      (String.append
        (String.append
          (String.append "this"%string (String.String (Ascii.ascii_of_nat 10) "string"%string))
          (String.String (Ascii.ascii_of_nat 10) "has"%string))
        (String.String (Ascii.ascii_of_nat 10) "mulntiple"%string))
      (String.String (Ascii.ascii_of_nat 10) "newlines"%string)
  ]
  (String.concat "" [
    String.append "hello"%string (String.String (Ascii.ascii_of_nat 10) "world"%string);
    String.append
      (String.append
        (String.append
          (String.append "this"%string (String.String (Ascii.ascii_of_nat 10) "string"%string))
          (String.String (Ascii.ascii_of_nat 10) "has"%string))
        (String.String (Ascii.ascii_of_nat 10) "multiple"%string))
      (String.String (Ascii.ascii_of_nat 10) "newlines"%string);
    "jumps"%string;
    String.append
      (String.append
        (String.append
          (String.append "this"%string (String.String (Ascii.ascii_of_nat 10) "string"%string))
          (String.String (Ascii.ascii_of_nat 10) "has"%string))
        (String.String (Ascii.ascii_of_nat 10) "multipule"%string))
      (String.String (Ascii.ascii_of_nat 10) "newlines"%string);
    String.append "hello"%string (String.String (Ascii.ascii_of_nat 10) "world"%string);
    String.append
      (String.append
        (String.append
          (String.append "this"%string (String.String (Ascii.ascii_of_nat 10) "string"%string))
          (String.String (Ascii.ascii_of_nat 10) "has"%string))
        (String.String (Ascii.ascii_of_nat 10) "mulntiple"%string))
      (String.String (Ascii.ascii_of_nat 10) "newlines"%string)
  ]).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.