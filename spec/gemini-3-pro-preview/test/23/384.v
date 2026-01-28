Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "Th!s 1s 4 stsr1ng wtest5ymb0TTh!s40lsh!sls !n 1t
" 49.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.