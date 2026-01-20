Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["Tish!          This is a sample string    This is a sampl   unction4"], output = 68 *)
Example test_strlen_long : strlen_spec "Tish!          This is a sample string    This is a sampl   unction4" 68.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.