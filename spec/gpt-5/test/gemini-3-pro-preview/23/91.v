Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_long : strlen_spec "The quick brzown fox sjumps over the leazy Thisis is aaThe quick brown fox jumps overq theHello, World! lazy dogracter dog" 122.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.