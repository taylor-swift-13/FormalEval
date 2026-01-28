Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "  te      1t  sThe    s tt \n Foxstr1str1ngng" 45.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.