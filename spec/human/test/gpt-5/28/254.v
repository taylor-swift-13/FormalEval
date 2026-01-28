Require Import List String Ascii.
Import ListNotations.
Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Definition nl : string := String (Ascii.ascii_of_nat 10) EmptyString.

Example problem_28_test: problem_28_spec
  [ ("hello"%string ++ nl ++ "world"%string);
    ("this"%string ++ nl ++ "string"%string ++ nl ++ "has"%string ++ nl ++ "multiple"%string ++ nl ++ "newlines"%string);
    ("jumps"%string);
    ("this"%string ++ nl ++ "string"%string ++ nl ++ "has"%string ++ nl ++ "multipule"%string ++ nl ++ "newlines"%string);
    ("hello"%string ++ nl ++ "w14orld"%string);
    ("hello"%string ++ nl ++ "world"%string);
    ("hello"%string ++ nl ++ "world"%string);
    ("hello"%string ++ nl ++ "world"%string)
  ]
  ( ("hello"%string ++ nl ++ "world"%string)
    ++ ("this"%string ++ nl ++ "string"%string ++ nl ++ "has"%string ++ nl ++ "multiple"%string ++ nl ++ "newlines"%string)
    ++ ("jumps"%string)
    ++ ("this"%string ++ nl ++ "string"%string ++ nl ++ "has"%string ++ nl ++ "multipule"%string ++ nl ++ "newlines"%string)
    ++ ("hello"%string ++ nl ++ "w14orld"%string)
    ++ ("hello"%string ++ nl ++ "world"%string)
    ++ ("hello"%string ++ nl ++ "world"%string)
    ++ ("hello"%string ++ nl ++ "world"%string)
  ).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.