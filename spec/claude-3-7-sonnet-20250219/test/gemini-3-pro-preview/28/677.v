Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec ["qu🧐ck"; "brown"; "spaces"; "fox"; "jumps"; "the"; "this
string
has
multiple
newlines"; "dog"] "qu🧐ckbrownspacesfoxjumpsthethis
string
has
multiple
newlinesdog".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.