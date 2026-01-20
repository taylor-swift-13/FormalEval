Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Import ListNotations.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition test_string : string :=
  string_of_list_ascii
    [Ascii.ascii_of_nat 32;
     Ascii.ascii_of_nat 224;
     Ascii.ascii_of_nat 232;
     Ascii.ascii_of_nat 236;
     Ascii.ascii_of_nat 242;
     Ascii.ascii_of_nat 249;
     Ascii.ascii_of_nat 225;
     Ascii.ascii_of_nat 233;
     Ascii.ascii_of_nat 237;
     Ascii.ascii_of_nat 243;
     Ascii.ascii_of_nat 250;
     Ascii.ascii_of_nat 253;
     Ascii.ascii_of_nat 226;
     Ascii.ascii_of_nat 234;
     Ascii.ascii_of_nat 238;
     Ascii.ascii_of_nat 244;
     Ascii.ascii_of_nat 105;
     Ascii.ascii_of_nat 119;
     Ascii.ascii_of_nat 84;
     Ascii.ascii_of_nat 105;
     Ascii.ascii_of_nat 115;
     Ascii.ascii_of_nat 104;
     Ascii.ascii_of_nat 33;
     Ascii.ascii_of_nat 33;
     Ascii.ascii_of_nat 49;
     Ascii.ascii_of_nat 116;
     Ascii.ascii_of_nat 104;
     Ascii.ascii_of_nat 251;
     Ascii.ascii_of_nat 227;
     Ascii.ascii_of_nat 241;
     Ascii.ascii_of_nat 245;
     Ascii.ascii_of_nat 228;
     Ascii.ascii_of_nat 235;
     Ascii.ascii_of_nat 239;
     Ascii.ascii_of_nat 246;
     Ascii.ascii_of_nat 252;
     Ascii.ascii_of_nat 255;
     Ascii.ascii_of_nat 231;
     Ascii.ascii_of_nat 32;
     Ascii.ascii_of_nat 32;
     Ascii.ascii_of_nat 10;
     Ascii.ascii_of_nat 10;
     Ascii.ascii_of_nat 119;
     Ascii.ascii_of_nat 116;
     Ascii.ascii_of_nat 101;
     Ascii.ascii_of_nat 115;
     Ascii.ascii_of_nat 116;
     Ascii.ascii_of_nat 53;
     Ascii.ascii_of_nat 121;
     Ascii.ascii_of_nat 109;
     Ascii.ascii_of_nat 98;
     Ascii.ascii_of_nat 52;
     Ascii.ascii_of_nat 48;
     Ascii.ascii_of_nat 108;
     Ascii.ascii_of_nat 115;
     Ascii.ascii_of_nat 32;
     Ascii.ascii_of_nat 32;
     Ascii.ascii_of_nat 32;
     Ascii.ascii_of_nat 32].

Example strlen_spec_new: strlen_spec test_string 59.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_new_Z: Z.of_nat (String.length test_string) = 59%Z.
Proof.
  simpl.
  reflexivity.
Qed.