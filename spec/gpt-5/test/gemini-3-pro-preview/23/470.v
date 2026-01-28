Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Fixpoint string_of_bytes (l : list nat) : string :=
  match l with
  | [] => EmptyString
  | n :: rest => String (ascii_of_nat n) (string_of_bytes rest)
  end.

Definition test_bytes : list nat := [
  224; 232; 236; 242; 249; 225; 233; 237; 243; 250; 253; 226; 234; 238; 244; 251; 227; 241; 245; 228; 235; 239; 246;
  224; 232; 236; 242; 249; 225; 233; 237; 243; 250; 253; 226; 234; 238; 244; 251; 227; 241; 245; 228; 235; 239; 246;
  252; 255; 231; 252; 255; 231
].

Example test_strlen_weird : strlen_spec (string_of_bytes test_bytes) 52.
Proof.
  unfold strlen_spec.
  vm_compute.
  reflexivity.
Qed.