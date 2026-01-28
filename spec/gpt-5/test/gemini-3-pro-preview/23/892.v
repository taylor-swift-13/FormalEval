Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_BBrownLaayLazystringunction : strlen_spec "BBrownLaayLazystringunction" 27.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.