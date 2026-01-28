Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["This"%string; "mucch"%string; "How"%string; "much"%string; "wood"%string; "would"%string; "a"%string; "chuck"%string; "if"%string; "a"%string; "woodchuck"%string; "could"%string; "wood"%string; "How"%string; "would"%string] ("ThismucchHowmuchwoodwouldachuckifawoodchuckcouldwoodHowwould"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.