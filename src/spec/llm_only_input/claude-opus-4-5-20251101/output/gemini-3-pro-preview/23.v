Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Example strlen_test_empty : strlen_spec "" 0.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

(* Additional example showing the result as Z (0%Z) as mentioned in the test case *)
Example strlen_test_empty_Z : Z.of_nat (String.length "") = 0%Z.
Proof.
  simpl.
  reflexivity.
Qed.