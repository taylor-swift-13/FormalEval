Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_TTBr_ownis: strlen_spec "TTBr ownis   " 13.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_TTBr_ownis_Z: Z.of_nat (String.length "TTBr ownis   ") = 13%Z.
Proof.
  simpl.
  reflexivity.
Qed.