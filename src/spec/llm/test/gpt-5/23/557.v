Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_sample: strlen_spec "Tish!          This is a sample string    This is a sampl   unction!n4" 70.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_sample_Z: Z.of_nat (String.length "Tish!          This is a sample string    This is a sampl   unction!n4") = 70%Z.
Proof.
  simpl.
  reflexivity.
Qed.