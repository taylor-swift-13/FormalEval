Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["Juom5ymbops"], output = 11 *)
Example test_strlen_Juom5ymbops : strlen_spec "Juom5ymbops" 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.