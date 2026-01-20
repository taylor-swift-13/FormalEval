Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_string: strlen_spec "Tihis sample string to      The     test the function"%string 53.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_string_Z: Z.of_nat (String.length "Tihis sample string to      The     test the function"%string) = 53%Z.
Proof.
  simpl.
  reflexivity.
Qed.