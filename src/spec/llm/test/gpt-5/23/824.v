Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_TTBrownnnis_spaces: strlen_spec "TTBrownnnis   " 14.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_TTBrownnnis_Z: Z.of_nat (String.length "TTBrownnnis   ") = 14%Z.
Proof.
  simpl.
  reflexivity.
Qed.