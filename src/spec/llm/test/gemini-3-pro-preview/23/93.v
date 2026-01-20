Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "The quick brzown fox jumps over the leazy Thisis is aaracter Hello, Woorld!dog" 78.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.