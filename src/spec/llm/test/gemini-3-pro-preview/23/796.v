Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation *)
Open Scope string_scope.

(* Test case: input = ["RDogmCLazyGGTk"], output = 14 *)
Example test_strlen_RDogmCLazyGGTk : strlen_spec "RDogmCLazyGGTk" 14.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.