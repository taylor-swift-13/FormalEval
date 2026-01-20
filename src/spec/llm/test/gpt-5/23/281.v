Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_whyNcJH1thfunnc: strlen_spec "whyNcJH1thfunnc"%string 15.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_whyNcJH1thfunnc_Z: Z.of_nat (String.length "whyNcJH1thfunnc"%string) = 15%Z.
Proof.
  simpl.
  reflexivity.
Qed.