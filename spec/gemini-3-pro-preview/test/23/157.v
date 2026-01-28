Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "Th!s 1s 4 str1ng wtest5ymb0ls !nsampleto 1t
" 44.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.