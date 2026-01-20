Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

Example test_strlen_long : strlen_spec "Juom5This is a sample string    This is a sampl            eto string to test the func Theon       to test the functionymbops" 125.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.