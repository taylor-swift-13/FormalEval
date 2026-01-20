Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_astr1ngsampl: strlen_spec "astr1ngsampl"%string 12.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_astr1ngsampl_Z: Z.of_nat (String.length "astr1ngsampl"%string) = 12%Z.
Proof.
  simpl.
  reflexivity.
Qed.