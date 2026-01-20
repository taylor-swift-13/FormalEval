Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_case :
  Spec ["How"; "much"; "wvSood"; "🦌"; "a"; "🐨"; "woodchuck"; "chuck"; "if"; "chuck"; "wood"; "wood"; "much"]
       "HowmuchwvSood🦌a🐨woodchuckchuckifchuckwoodwoodmuch".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.