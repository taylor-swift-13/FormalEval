Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_quick_parrot :
  problem_28_spec ["quick"; "🦜"; "144"; "Hello, World!"; "sovertrings"] "quick🦜144Hello, World!sovertrings".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.