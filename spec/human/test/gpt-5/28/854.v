Require Import List String Ascii.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec
  ["313"%string;
   String.append "this"%string
     (String.String (Ascii.ascii_of_nat 10)
       (String.append "string"%string
         (String.String (Ascii.ascii_of_nat 10)
           (String.append "has"%string
             (String.String (Ascii.ascii_of_nat 10)
               (String.append "multiple"%string
                 (String.String (Ascii.ascii_of_nat 10) "newlines"%string)))))))]
  (String.append "313"%string
   (String.append "this"%string
     (String.String (Ascii.ascii_of_nat 10)
       (String.append "string"%string
         (String.String (Ascii.ascii_of_nat 10)
           (String.append "has"%string
             (String.String (Ascii.ascii_of_nat 10)
               (String.append "multiple"%string
                 (String.String (Ascii.ascii_of_nat 10) "newlines"%string))))))))).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.