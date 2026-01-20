Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_BBrownLaayLazy_spaces: strlen_spec "BBrownLaayLazy  "%string 16.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_BBrownLaayLazy_spaces_Z: Z.of_nat (String.length "BBrownLaayLazy  "%string) = 16%Z.
Proof.
  simpl.
  reflexivity.
Qed.