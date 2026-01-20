Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_rrstr1ng: strlen_spec "rrstr1ng" 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_rrstr1ng_Z: Z.of_nat (String.length "rrstr1ng") = 8%Z.
Proof.
  simpl.
  reflexivity.
Qed.