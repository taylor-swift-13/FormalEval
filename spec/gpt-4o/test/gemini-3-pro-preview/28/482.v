Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec ["woood"; "How"; "much"; "wood"; "into"; "would"; "a"; "woodchuck"; "chuck"; "if"; "a"; "woodchuck"; "coucouldthis
ce
newlinesld"; "chuck"; "wood"; "wood"; "much"; "a"] "wooodHowmuchwoodintowouldawoodchuckchuckifawoodchuckcoucouldthis
ce
newlinesldchuckwoodwoodmucha".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.