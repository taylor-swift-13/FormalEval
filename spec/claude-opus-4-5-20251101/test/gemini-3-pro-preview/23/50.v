Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat. (* Replaces incorrect Coq.Numbers.Natural.Peano.NPeano *)

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_long : strlen_spec "The quick brzown fox sjumps over the leazy Thisis is aaracter dog" 65.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.