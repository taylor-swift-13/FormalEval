Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_sampLazyle: strlen_spec "sampLazyle" 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_sampLazyle_Z: Z.of_nat (String.length "sampLazyle") = 10%Z.
Proof.
  simpl.
  reflexivity.
Qed.