Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

Example test_strlen_complex : strlen_spec "The quick brown fox11234567890 jumps over the lazy This striThis is aaracter dog" 80.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.