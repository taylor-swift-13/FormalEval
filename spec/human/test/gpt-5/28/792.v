Require Import List String Ascii.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec
  ["123"%string;
   "456"%string;
   ("456no"%string ++ String.String (Ascii.ascii_of_nat 10) String.EmptyString ++ "newline"%string ++ String.String (Ascii.ascii_of_nat 10) String.EmptyString ++ "this"%string ++ String.String (Ascii.ascii_of_nat 10) String.EmptyString ++ "is"%string ++ String.String (Ascii.ascii_of_nat 10) String.EmptyString ++ "a.."%string ++ String.String (Ascii.ascii_of_nat 10) String.EmptyString ++ "long"%string ++ String.String (Ascii.ascii_of_nat 10) String.EmptyString ++ "string"%string)%string;
   "10"%string;
   "11"%string;
   "12"%string;
   "13"%string;
   "144"%string;
   "15"%string;
   "1"%string;
   "17"%string]
  ("123"%string ++
   "456"%string ++
   ("456no"%string ++ String.String (Ascii.ascii_of_nat 10) String.EmptyString ++ "newline"%string ++ String.String (Ascii.ascii_of_nat 10) String.EmptyString ++ "this"%string ++ String.String (Ascii.ascii_of_nat 10) String.EmptyString ++ "is"%string ++ String.String (Ascii.ascii_of_nat 10) String.EmptyString ++ "a.."%string ++ String.String (Ascii.ascii_of_nat 10) String.EmptyString ++ "long"%string ++ String.String (Ascii.ascii_of_nat 10) String.EmptyString ++ "string"%string)%string ++
   "10"%string ++
   "11"%string ++
   "12"%string ++
   "13"%string ++
   "144"%string ++
   "15"%string ++
   "1"%string ++
   "17"%string)%string.
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.