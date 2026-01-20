Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["sJTh!s 1s 4 str1ng wtest5ymb0ls !nsampleto 1t\num5ymb0lsmfunctionJummtop    This is a sample sttotherintg to test the function      QuaOverick     s"], output = 147 *)
Example test_strlen_complex : strlen_spec ("sJTh!s 1s 4 str1ng wtest5ymb0ls !nsampleto 1t" ++ String (ascii_of_nat 10) "um5ymb0lsmfunctionJummtop    This is a sample sttotherintg to test the function      QuaOverick     s") 147.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.