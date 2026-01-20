Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_spaces: strlen_spec "    1t 1 Thestring    "%string 22.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_spaces_Z: Z.of_nat (String.length "    1t 1 Thestring    "%string) = 22%Z.
Proof.
  simpl.
  reflexivity.
Qed.