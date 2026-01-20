Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_empty : strlen_spec "" 0.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

(* Additional example showing the result as Z if needed *)
Example test_strlen_empty_Z : Z.of_nat (String.length "") = 0%Z.
Proof.
  simpl.
  reflexivity.
Qed.