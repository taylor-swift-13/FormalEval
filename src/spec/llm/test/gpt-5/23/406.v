Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_str1ngsampaOverl: strlen_spec "str1ngsampaOverl" 16.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_str1ngsampaOverl_Z: Z.of_nat (String.length "str1ngsampaOverl") = 16%Z.
Proof.
  simpl.
  reflexivity.
Qed.