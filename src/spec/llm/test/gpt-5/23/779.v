Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_Thi: strlen_spec "Thi" 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_Thi_Z: Z.of_nat (String.length "Thi") = 3%Z.
Proof.
  simpl.
  reflexivity.
Qed.