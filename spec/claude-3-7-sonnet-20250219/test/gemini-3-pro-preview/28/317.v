Require Import List.
Require Import String.
Require Import Ascii.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Definition nl := String (ascii_of_nat 10) "".

Definition s1 := "t!!shis" ++ nl ++ "string" ++ nl ++ "has" ++ nl ++ "multiple" ++ nl ++ "newlines".
Definition s2 := "t!!his" ++ nl ++ "string" ++ nl ++ "has" ++ nl ++ "multiple" ++ nl ++ "newlines".
Definition s3 := "hello" ++ nl ++ "world".
Definition s4 := "this" ++ nl ++ "string" ++ nl ++ "has" ++ nl ++ "multiple" ++ nl ++ "newlines".
Definition s5 := "jumps".
Definition s6 := "t!!his" ++ nl ++ "string" ++ nl ++ "has" ++ nl ++ "multiple" ++ nl ++ "newlines".
Definition s7 := "t!!his" ++ nl ++ "string" ++ nl ++ "has" ++ nl ++ "multiple" ++ nl ++ "newlines".

Example test_concatenate_newlines: concatenate_spec 
  [s1; s2; s3; s4; s5; s6; s7] 
  (s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s6 ++ s7).
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.