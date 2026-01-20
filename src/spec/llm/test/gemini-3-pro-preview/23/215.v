Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["   \nhy    This is a sample strinisg to test the fuunction          NcJH\n  string"], output = 80 *)
Example test_strlen_complex : strlen_spec "   
hy    This is a sample strinisg to test the fuunction          NcJH
  string" 80.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.