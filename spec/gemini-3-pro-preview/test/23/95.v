Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

Example test_strlen_complex : strlen_spec ("1234 This sitriThis is a long string that has many characters in itng has a " ++ String (ascii_of_nat 10) " neThe quick brown f ox jumps over the lazygwline character5") 137.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.