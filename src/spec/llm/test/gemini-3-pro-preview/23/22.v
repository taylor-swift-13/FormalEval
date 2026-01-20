Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["one
twot
three
four
five"], output = 24 *)
(* Note: Although the prompt mentions 24%Z, the specification defines res as nat, 
   so we use the natural number 24 to ensure type correctness. *)
Example test_strlen_multiline : strlen_spec "one
twot
three
four
five" 24.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.