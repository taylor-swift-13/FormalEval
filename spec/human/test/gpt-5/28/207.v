Require Import List String Ascii.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec [String.append "hello"%string (String (Ascii.ascii_of_nat 10) "world"%string)] (String.append "hello"%string (String (Ascii.ascii_of_nat 10) "world"%string)).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.