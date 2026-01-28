Require Import List String Ascii.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec 
  [ "123"
  ; "133"
  ; "456"
  ; "456no" ++ String (ascii_of_nat 10) ("newline" ++ String (ascii_of_nat 10) ("this" ++ String (ascii_of_nat 10) ("is" ++ String (ascii_of_nat 10) ("a.." ++ String (ascii_of_nat 10) ("long" ++ String (ascii_of_nat 10) "string")))))
  ; "abc878Dr" ++ String (ascii_of_nat 240) (String (ascii_of_nat 159) (String (ascii_of_nat 166) (String (ascii_of_nat 155) "9d")))
  ; "10"
  ; "3jupmps"
  ; "11"
  ; "12"
  ; "13"
  ; "144"
  ; "15"
  ; "1"
  ; "abc8789d"
  ; "15"
  ]
  ( "123" ++ "133" ++ "456" ++
    ("456no" ++ String (ascii_of_nat 10) ("newline" ++ String (ascii_of_nat 10) ("this" ++ String (ascii_of_nat 10) ("is" ++ String (ascii_of_nat 10) ("a.." ++ String (ascii_of_nat 10) ("long" ++ String (ascii_of_nat 10) "string")))))) ++
    ("abc878Dr" ++ String (ascii_of_nat 240) (String (ascii_of_nat 159) (String (ascii_of_nat 166) (String (ascii_of_nat 155) "9d")))) ++
    "10" ++ "3jupmps" ++ "11" ++ "12" ++ "13" ++ "144" ++ "15" ++ "1" ++ "abc8789d" ++ "15"
  ).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.