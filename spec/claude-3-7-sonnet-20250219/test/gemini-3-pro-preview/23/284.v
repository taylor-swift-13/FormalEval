Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Fixpoint codes_to_string (l : list nat) : string :=
  match l with
  | [] => EmptyString
  | n :: ns => String (ascii_of_nat n) (codes_to_string ns)
  end.

Definition input_str := 
  String.append 
    "Th!s40ls !n 1This is a sample string    This is a sampl            eto string to LqNCZAtest the func Theon           to test the functi           "
    (String.append 
      (codes_to_string [224; 232; 236; 242; 249; 225; 233; 237; 243; 250; 253; 226; 234; 238; 244; 251; 227; 241; 245; 228; 235; 239; 246; 252; 255; 231])
      "nt
").

Example test_strlen_complex : strlen_spec input_str 175.
Proof.
  unfold strlen_spec.
  unfold input_str.
  vm_compute.
  reflexivity.
Qed.