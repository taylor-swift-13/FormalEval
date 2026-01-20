Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

Example test_strlen_complex : strlen_spec "  Th!s 1s 4 st1r1ng wtest5nymb0ls !nsampleto 1t
" 48.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.