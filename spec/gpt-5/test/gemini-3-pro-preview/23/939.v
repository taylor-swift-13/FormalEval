Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_case1 : strlen_spec "  te      1t  sThe    s tt 
1 Foxstr1str1ngng" 45.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.