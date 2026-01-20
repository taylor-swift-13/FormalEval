Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["Hello, Woorlod!"], output = 15 *)
Example test_strlen_hello : strlen_spec "Hello, Woorlod!" 15.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.