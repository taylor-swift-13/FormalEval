Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_aLLaa_zz_aaick: strlen_spec "aLLaa zz aaick" 14.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_aLLaa_zz_aaick_Z: Z.of_nat (String.length "aLLaa zz aaick") = 14%Z.
Proof.
  simpl.
  reflexivity.
Qed.