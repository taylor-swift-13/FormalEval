Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "JTh!s 1s 4 str1ng wtest5ymb0ls !nsampleto 1t
um5ymb0lsmfunction" 63.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.