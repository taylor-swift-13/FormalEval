Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["  Tish!           4!n \n\n  1s  "], output = 30 *)
Example test_strlen_complex : strlen_spec "  Tish!           4!n 

  1s  " 30.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.