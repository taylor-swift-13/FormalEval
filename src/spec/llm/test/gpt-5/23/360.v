Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_Tishstrintgi_s4: strlen_spec "Tishstrintgi        s4" 22.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_Tishstrintgi_s4_Z: Z.of_nat (String.length "Tishstrintgi        s4") = 22%Z.
Proof.
  simpl.
  reflexivity.
Qed.