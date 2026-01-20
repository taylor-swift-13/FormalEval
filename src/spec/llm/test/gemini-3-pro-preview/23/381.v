Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_case1 : strlen_spec "  Th!s 1s 4 str1ng wtest5nymb0ls !nsampleto 1t
" 47.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.