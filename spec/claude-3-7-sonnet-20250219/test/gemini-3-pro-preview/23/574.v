Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Fixpoint codes_to_string (l : list nat) : string :=
  match l with
  | [] => EmptyString
  | n :: ns => String (ascii_of_nat n) (codes_to_string ns)
  end.

Example test_strlen_complex : strlen_spec (codes_to_string [68; 235; 224; 232; 236; 242; 249; 104; 121; 78; 74; 99; 74; 245; 228; 235; 239; 255; 231; 103]) 20.
Proof.
  unfold strlen_spec.
  vm_compute.
  reflexivity.
Qed.