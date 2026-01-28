Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate : concatenate_spec ["How"; "much"; "wood"; "🦌a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "could"; "chuck"; "wood"; "1amuchb0chuck"; "woodchuck"; "much"; "chuck"; "woodchuck"] "Howmuchwood🦌awoodchuckchuckifawoodchuckcouldchuckwood1amuchb0chuckwoodchuckmuchchuckwoodchuck".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.