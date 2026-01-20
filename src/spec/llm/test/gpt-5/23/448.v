Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_Juom5ymbops: strlen_spec "Juom5ymbops" 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_Juom5ymbops_Z: Z.of_nat (String.length "Juom5ymbops") = 11%Z.
Proof.
  simpl.
  reflexivity.
Qed.