Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["🐻"%string; "🦊"%string; "quick"%string; "🐼"%string; "🐯"%string; "🦛"%string; "18"%string; "🦌"%string; "🦢"%string; "🦉"%string; "could🐢"%string; "!!"%string; "🐢"%string; "🦉"%string] ("🐻🦊quick🐼🐯🦛18🦌🦢🦉could🐢!!🐢🦉"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.