Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_concatenate_long :
  problem_28_spec ["Scissorslanguage"; "Helloo"; "Hello"; "wordld"; "world"; "wordld"] "ScissorslanguageHellooHellowordldworldwordld".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.