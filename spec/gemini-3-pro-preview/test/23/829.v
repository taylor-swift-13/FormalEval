Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["BrozwnLazys"], output = 11 *)
Example test_strlen_BrozwnLazys : strlen_spec "BrozwnLazys" 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.