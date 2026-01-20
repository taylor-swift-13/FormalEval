Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_wwhyNcJH1thfunnchy1N: strlen_spec "wwhyNcJH1thfunnchy1N" 20.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_wwhyNcJH1thfunnchy1N_Z: Z.of_nat (String.length "wwhyNcJH1thfunnchy1N") = 20%Z.
Proof.
  simpl.
  reflexivity.
Qed.