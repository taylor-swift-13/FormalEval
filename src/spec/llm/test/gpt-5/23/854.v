Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_TBrowMNhqmnrownisgmCV: strlen_spec "TBrowMNhqmnrownisgmCV"%string 21.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_TBrowMNhqmnrownisgmCV_Z: Z.of_nat (String.length "TBrowMNhqmnrownisgmCV"%string) = 21%Z.
Proof.
  simpl.
  reflexivity.
Qed.