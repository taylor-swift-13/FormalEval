Require Import List String Ascii.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec
  [
    "chara1longcters"%string;
    ("hello"%string ++ String (Ascii.ascii_of_nat 10) "world"%string)%string;
    "characters"%string;
    ("no"%string
      ++ String (Ascii.ascii_of_nat 10) ""%string
      ++ "newline"%string
      ++ String (Ascii.ascii_of_nat 10) ""%string
      ++ "this"%string
      ++ String (Ascii.ascii_of_nat 10) ""%string
      ++ "is"%string
      ++ String (Ascii.ascii_of_nat 10) ""%string
      ++ "a.."%string
      ++ String (Ascii.ascii_of_nat 10) ""%string
      ++ "long"%string
      ++ String (Ascii.ascii_of_nat 10) ""%string
      ++ "string"%string
    )%string;
    "has"%string;
    ("this"%string
      ++ String (Ascii.ascii_of_nat 10) ""%string
      ++ "string"%string
      ++ String (Ascii.ascii_of_nat 10) ""%string
      ++ "has"%string
      ++ String (Ascii.ascii_of_nat 10) ""%string
      ++ "multiple"%string
      ++ String (Ascii.ascii_of_nat 10) ""%string
      ++ "newlines"%string
    )%string
  ]
  (
    ("chara1longcters"%string
     ++ "hello"%string ++ String (Ascii.ascii_of_nat 10) "world"%string
     ++ "characters"%string
     ++ "no"%string
     ++ String (Ascii.ascii_of_nat 10) ""%string
     ++ "newline"%string
     ++ String (Ascii.ascii_of_nat 10) ""%string
     ++ "this"%string
     ++ String (Ascii.ascii_of_nat 10) ""%string
     ++ "is"%string
     ++ String (Ascii.ascii_of_nat 10) ""%string
     ++ "a.."%string
     ++ String (Ascii.ascii_of_nat 10) ""%string
     ++ "long"%string
     ++ String (Ascii.ascii_of_nat 10) ""%string
     ++ "string"%string
     ++ "has"%string
     ++ "this"%string
     ++ String (Ascii.ascii_of_nat 10) ""%string
     ++ "string"%string
     ++ String (Ascii.ascii_of_nat 10) ""%string
     ++ "has"%string
     ++ String (Ascii.ascii_of_nat 10) ""%string
     ++ "multiple"%string
     ++ String (Ascii.ascii_of_nat 10) ""%string
     ++ "newlines"%string
    )%string
  ).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.