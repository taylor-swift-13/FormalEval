Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "Th!s 1s 4 sTtTheTer1ng wtest5ymb0lse !n 1t
Jum5ymb0lsmfunct ion" 63.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.