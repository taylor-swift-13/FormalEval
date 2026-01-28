Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen : strlen_spec "The quick brzown fox sjumps over the leazy Thisis is aaracter dog" 65.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.