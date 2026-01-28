Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["How"%string; "much"%string; "would"%string; "woodchuck"%string; "chuck"%string; "if"%string; "if"%string; "wook"%string; "could"%string; "chuck"%string; "wowoquvSickod"%string; "much"%string; "woodchuock"%string; "would"%string; "woodchuck"%string] ("HowmuchwouldwoodchuckchuckififwookcouldchuckwowoquvSickodmuchwoodchuockwouldwoodchuck"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.