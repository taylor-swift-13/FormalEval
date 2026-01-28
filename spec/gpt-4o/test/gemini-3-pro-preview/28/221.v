Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec ["How"; "much"; "wowod"; "a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "How"] "HowmuchwowodawoodchuckchuckifawoodchuckcouldchuckHow".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.