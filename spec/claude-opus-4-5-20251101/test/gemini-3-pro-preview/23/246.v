Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat. (* Replaces incorrect Coq.Numbers.Natural.Peano.NPeano *)

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_long : strlen_spec "This is a sample string    This is a sampl            eto string to test the func Theon       to test the function" 114.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.