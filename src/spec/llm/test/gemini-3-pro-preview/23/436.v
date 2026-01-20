Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_case1 : strlen_spec "Th!s 1s str1ng wtest5ymb0ls !n 1t
" 34.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.