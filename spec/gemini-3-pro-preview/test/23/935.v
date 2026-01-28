Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["s    \n\n !func!ntio    \n\n func!ntion  n  e"], output = 41 *)
Example test_strlen_complex : strlen_spec "s    

 !func!ntio    

 func!ntion  n  e" 41.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.