Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_hello : strlen_spec "Hello, Woorlod!" 15.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.