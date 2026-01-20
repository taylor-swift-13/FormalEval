Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_TThs40lshs: strlen_spec "TTh!s40lsh!s"%string 12.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_TThs40lshs_Z: Z.of_nat (String.length "TTh!s40lsh!s"%string) = 12%Z.
Proof.
  simpl.
  reflexivity.
Qed.