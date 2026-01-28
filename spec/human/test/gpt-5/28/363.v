Require Import List String Ascii.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec
  [String.append "hello"%string (String (Ascii.ascii_of_nat 10) "world"%string);
   "jum"%string; "jumps"%string; "jumps"%string]
  (String.append
     (String.append "hello"%string (String (Ascii.ascii_of_nat 10) "world"%string))
     (String.append "jum"%string (String.append "jumps"%string "jumps"%string))).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.