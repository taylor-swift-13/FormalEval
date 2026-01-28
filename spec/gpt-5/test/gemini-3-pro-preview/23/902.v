Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "  te      1t  sThe    s tt \n Foxstr1str1ngng " 46.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.