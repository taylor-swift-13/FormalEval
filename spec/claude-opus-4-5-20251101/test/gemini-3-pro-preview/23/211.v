Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat. (* Replaces incorrect Coq.Numbers.Natural.Peano.NPeano *)
Import ListNotations.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Definition test_codes : list nat := [
  116; 110; 32; 227; 32; 32; 32; 32; 32; 32; 32; 32; 32; 32;
  224; 232; 236; 242; 249; 225; 233; 237; 243; 250; 253; 226;
  234; 238; 244; 251; 227; 241; 245; 228; 235; 239; 246; 252;
  255; 231
].

Fixpoint construct_string (l : list nat) : string :=
  match l with
  | [] => EmptyString
  | n :: ns => String (ascii_of_nat n) (construct_string ns)
  end.

Definition test_input : string := construct_string test_codes.

Example test_strlen_complex : strlen_spec test_input 40.
Proof.
  unfold strlen_spec.
  vm_compute.
  reflexivity.
Qed.