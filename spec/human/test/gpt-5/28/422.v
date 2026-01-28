Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["This"%string; "mucch"%string; "How"%string; "woo🦛🦛dchuck"%string; "much"%string; "wood0"%string; "would"%string; "a"%string; "chuck"%string; "Howmuhch"%string; "if"%string; "a"%string; "woodchuck"%string; "could"%string; "wood"%string; "How"%string] ("ThismucchHowwoo🦛🦛dchuckmuchwood0wouldachuckHowmuhchifawoodchuckcouldwoodHow"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.