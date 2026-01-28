Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_sentence : strlen_spec "The quick brzown fox jumps over the leazy Thisis is aaracter dog" 64.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.