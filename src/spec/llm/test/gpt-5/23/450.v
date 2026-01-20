Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_whyNcJH1funnc: strlen_spec "whyNcJH1funnc" 13.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_whyNcJH1funnc_Z: Z.of_nat (String.length "whyNcJH1funnc") = 13%Z.
Proof.
  simpl.
  reflexivity.
Qed.