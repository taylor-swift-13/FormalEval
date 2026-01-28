Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_TBrowMNhqmnrownisgmCV : strlen_spec "TBrowMNhqmnrownisgmCV" 21.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.