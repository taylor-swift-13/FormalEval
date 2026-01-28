Require Import List String Ascii.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec
  ["12"%string;
   "jumwowoquvSickod"%string;
   "multipule"%string;
   "jum"%string;
   String.concat "" ["this"%string; String (Ascii.ascii_of_nat 10) EmptyString; "string"%string; String (Ascii.ascii_of_nat 10) EmptyString; "has"%string; String (Ascii.ascii_of_nat 10) EmptyString; "multiple"%string; String (Ascii.ascii_of_nat 10) EmptyString; "newlines"%string];
   "wooodjum"%string;
   "jumps"%string;
   "th6is"%string;
   "jumps"%string;
   "12"%string]
  (String.concat ""
     ["12"%string;
      "jumwowoquvSickod"%string;
      "multipule"%string;
      "jum"%string;
      String.concat "" ["this"%string; String (Ascii.ascii_of_nat 10) EmptyString; "string"%string; String (Ascii.ascii_of_nat 10) EmptyString; "has"%string; String (Ascii.ascii_of_nat 10) EmptyString; "multiple"%string; String (Ascii.ascii_of_nat 10) EmptyString; "newlines"%string];
      "wooodjum"%string;
      "jumps"%string;
      "th6is"%string;
      "jumps"%string;
      "12"%string]).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.