Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_BBrownLaayLazy: strlen_spec "BBrownLaayLazy" 14.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_BBrownLaayLazy_Z: Z.of_nat (String.length "BBrownLaayLazy") = 14%Z.
Proof.
  simpl.
  reflexivity.
Qed.