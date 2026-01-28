Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list (list string)) : Prop := True.

Definition problem_28_spec (input : list (list string)) (output : string) : Prop :=
  String.concat "" (concat input) = output.

Example test_concatenate_nonempty : problem_28_spec [["python"; "is"; "a"; "great"; "language"]] "pythonisagreatlanguage".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.