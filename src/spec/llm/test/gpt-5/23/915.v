Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_TTBrownis_spaces: strlen_spec "TTBrownis    "%string 13.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_TTBrownis_spaces_Z: Z.of_nat (String.length "TTBrownis    "%string) = 13%Z.
Proof.
  simpl.
  reflexivity.
Qed.