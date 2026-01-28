Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_concatenate_scissors :
  problem_28_spec ["Scissors"; "python"; "a"; "great"; "language"; "language"] "Scissorspythonagreatlanguagelanguage".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.