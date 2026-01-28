Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec 
  [ "chara1longcters"
  ; "hello\nworld"
  ; "characters"
  ; "no\nnewline\nthis\nis\na..\nlong\nstring"
  ; "has"
  ; "this\nstring\nhas\nmultiple\nnewlines"
  ]
  "chara1longctershello\nworldcharactersno\nnewline\nthis\nis\na..\nlong\nstringhasthis\nstring\nhas\nmultiple\nnewlines".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.