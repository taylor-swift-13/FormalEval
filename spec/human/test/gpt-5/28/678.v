Require Import List String Ascii.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Definition nl : string := String.String (Ascii.ascii_of_nat 10) String.EmptyString.

Example problem_28_test: problem_28_spec
  [
    String.append "hello"%string (String.append nl "wrld"%string);
    String.append "this"%string (String.append nl (String.append "string"%string (String.append nl (String.append "has"%string (String.append nl (String.append "multiple"%string (String.append nl "newlines"%string)))))));
    String.append "no"%string (String.append nl (String.append "newline"%string (String.append nl (String.append "this"%string (String.append nl (String.append "is"%string (String.append nl (String.append "a.."%string (String.append nl (String.append "long"%string (String.append nl "string"%string)))))))))));
    String.append "this"%string (String.append nl (String.append "string"%string (String.append nl (String.append "has"%string (String.append nl (String.append "multiple"%string (String.append nl "newlines"%string)))))))
  ]
  (String.append
     (String.append "hello"%string (String.append nl "wrld"%string))
     (String.append
        (String.append "this"%string (String.append nl (String.append "string"%string (String.append nl (String.append "has"%string (String.append nl (String.append "multiple"%string (String.append nl "newlines"%string))))))))
        (String.append
           (String.append "no"%string (String.append nl (String.append "newline"%string (String.append nl (String.append "this"%string (String.append nl (String.append "is"%string (String.append nl (String.append "a.."%string (String.append nl (String.append "long"%string (String.append nl "string"%string))))))))))))
           (String.append "this"%string (String.append nl (String.append "string"%string (String.append nl (String.append "has"%string (String.append nl (String.append "multiple"%string (String.append nl "newlines"%string))))))))))).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.