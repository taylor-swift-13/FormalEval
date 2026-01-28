Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat. (* Replaces incorrect Coq.Numbers.Natural.Peano.NPeano *)

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_complex : strlen_spec 
  ("Testing te stingone" ++ String (ascii_of_nat 10) "" ++ 
   "twot" ++ String (ascii_of_nat 10) "" ++ 
   "thrThis is a long string that has many characters in itee" ++ String (ascii_of_nat 10) "" ++ 
   "four" ++ String (ascii_of_nat 10) "" ++ 
   "five 123") 96.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.