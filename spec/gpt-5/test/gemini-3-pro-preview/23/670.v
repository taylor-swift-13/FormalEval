Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_this_nction : strlen_spec "This nction" 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.