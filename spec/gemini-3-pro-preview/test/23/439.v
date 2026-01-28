Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

Example test_strlen_newlines : strlen_spec ("f" ++ String (ascii_of_nat 10) (String (ascii_of_nat 10) "fnunc")) 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.