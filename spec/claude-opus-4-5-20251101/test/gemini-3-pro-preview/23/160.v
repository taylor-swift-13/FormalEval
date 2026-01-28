Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat. (* Replaces incorrect Coq.Numbers.Natural.Peano.NPeano *)

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Fixpoint codes_to_string (l : list nat) : string :=
  match l with
  | [] => EmptyString
  | n :: t => String (ascii_of_nat n) (codes_to_string t)
  end.

Definition input_str : string := codes_to_string [
  68; 224; 232; 236; 242; 249; 52; 225; 233; 237; 243; 250; 253; 226; 234; 238; 
  244; 251; 227; 241; 245; 228; 235; 239; 246; 252; 255; 231; 103; 111; 103
].

Example test_strlen_complex : strlen_spec input_str 31.
Proof.
  unfold strlen_spec.
  unfold input_str.
  vm_compute.
  reflexivity.
Qed.