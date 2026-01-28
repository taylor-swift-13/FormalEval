Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Import Nat.

Definition is_digit_bool (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (nat_of_ascii "0"%char <=? n) && (n <=? nat_of_ascii "9"%char).

Definition is_alpha (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (nat_of_ascii "a"%char <= n /\ n <= nat_of_ascii "z"%char) \/
  (nat_of_ascii "A"%char <= n /\ n <= nat_of_ascii "Z"%char).

Definition problem_141_spec (file_name_str : string) (result : string) : Prop :=
  let file_name := list_ascii_of_string file_name_str in
  let is_valid :=
    (length (filter is_digit_bool file_name) <= 3) /\
    (exists prefix suffix,
      file_name = prefix ++ "."%char :: suffix /\
      ~ In "."%char (prefix ++ suffix) /\
      (exists first_char rest_prefix,
        prefix = first_char :: rest_prefix /\ is_alpha first_char) /\
      (suffix = ("t"::"x"::"t"::[])%char \/
       suffix = ("e"::"x"::"e"::[])%char \/
       suffix = ("d"::"l"::"l"::[])%char))
  in
  (is_valid /\ result = "Yes") \/
  (~is_valid /\ result = "No").

Example example_txt_valid : problem_141_spec "example.txt" "Yes".
Proof.
  unfold problem_141_spec.
  left.
  split.
  - unfold is_valid.
    split.
    + compute.
      reflexivity.
    + exists [ "e"; "x"; "a"; "m"; "p"; "l"; "e" ]%char.
      exists [ "t"; "x"; "t" ]%char.
      split.
      * compute.
        reflexivity.
      * split.
        { intro H.
          compute in H.
          destruct H as [H | [H | [H | [H | [H | [H | [H | [H | [H | [H]]]]]]]]]].
          all: discriminate H. }
        split.
        { exists "e"%char.
          exists [ "x"; "a"; "m"; "p"; "l"; "e" ]%char.
          split.
          - compute.
            reflexivity.
          - unfold is_alpha.
            left.
            split.
            + compute.
              lia.
            + compute.
              lia. }
        { left.
          compute.
          reflexivity. }
  - compute.
    reflexivity.
Qed.