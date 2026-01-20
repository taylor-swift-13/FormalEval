Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_1 : strlen_spec "  Th!s 1s 4 str1ng wtest5ymb0ls !nsampleto 1t
" 46.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.