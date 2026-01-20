Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["one..."], output = 154 *)
Example test_strlen_long : strlen_spec "one
twota
thrThis is a long string that has many chone
twot
thrThis is a long string that has  many characters in itee
four
fivearacters in itee
four
five" 154.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.