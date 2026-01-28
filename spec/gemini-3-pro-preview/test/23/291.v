Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "   

wwtes            ls   Th!s 1s 4 str1ng wtest5ymb0ls !n 1t
 " 64.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.