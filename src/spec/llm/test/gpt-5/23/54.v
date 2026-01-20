Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_oef_ffoive: strlen_spec "oef
ffoive" 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_oef_ffoive_Z: Z.of_nat (String.length "oef
ffoive") = 10%Z.
Proof.
  simpl.
  reflexivity.
Qed.