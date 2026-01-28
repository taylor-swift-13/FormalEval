Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Fixpoint string_of_bytes (l : list nat) : string :=
  match l with
  | [] => EmptyString
  | n :: l' => String (ascii_of_nat n) (string_of_bytes l')
  end.

Definition test_input := string_of_bytes [
  84;104;105;115;32;105;115;32;97;32;115;97;109;112;108;101;32;115;116;114;105;110;103;32;32;32;32;84;104;105;115;32;105;115;32;97;32;115;97;109;112;108;32;32;32;32;32;32;32;32;32;32;32;32;101;116;111;32;115;116;114;105;110;103;32;116;111;32;116;101;115;116;32;116;104;76;97;
  224;232;236;242;249;225;104;233;237;243;250;249;253;226;234;32;32;32;
  10;10;
  32;32;66;114;111;49;115;32;32;
  238;244;251;227;241;245;228;235;239;246;252;255;231;
  81;70;111;81;120;119;116;101;115;116;53;121;109;98;48;108;115;101;117;107;121;105;99;107;121;116;104;101;32;102;117;110;99;116;105;111;110
].

Example test_strlen_complex : strlen_spec test_input 156.
Proof.
  unfold strlen_spec.
  vm_compute.
  reflexivity.
Qed.