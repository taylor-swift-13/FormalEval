Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Fixpoint nats_to_string (l : list nat) : string :=
  match l with
  | [] => EmptyString
  | n :: t => String (ascii_of_nat n) (nats_to_string t)
  end.

Definition test_input : string :=
  nats_to_string [32; 224; 232; 236; 242; 249; 225; 233; 237; 243; 250; 253; 226; 234; 238; 244; 105; 119; 84; 105; 115; 104; 33; 33; 49; 116; 104; 251; 227; 241; 245; 228; 235; 239; 246; 252; 255; 231; 32; 32; 10; 10; 119; 116; 101; 115; 116; 53; 121; 109; 98; 52; 48; 108; 115; 32; 32; 32; 32].

Example test_strlen_59 : strlen_spec test_input 59.
Proof.
  unfold strlen_spec.
  unfold test_input.
  vm_compute.
  reflexivity.
Qed.