Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["This is a sample string    This is a sampl            eto string to LqNCZAtest the func Theon           to test the function"], output = 124 *)
Example test_strlen_long : strlen_spec "This is a sample string    This is a sampl            eto string to LqNCZAtest the func Theon           to test the function" 124.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.