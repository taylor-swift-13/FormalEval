Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "   This is a sample string to test th e function

   z" 54.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.