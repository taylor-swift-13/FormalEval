Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec "TMNhqmCVhis is ao sample starintog ton test the n" 49.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.