Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.
Import Nat.

Definition is_digit_bool (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (nat_of_ascii "0"%char <=? n) && (n <=? nat_of_ascii "9"%char).

Definition is_alpha (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (nat_of_ascii "a"%char <= n /\ n <= nat_of_ascii "z"%char) \/
  (nat_of_ascii "A"%char <= n /\ n <= nat_of_ascii "Z"%char).

Definition problem_141_pre (file_name : string) : Prop := True.

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
  (is_valid /\ result = "Yes"%string) \/
  (~is_valid /\ result = "No"%string).

Example problem_141_test_1script_bat :
  problem_141_spec "1script.bat"%string "No"%string.
Proof.
  unfold problem_141_spec.
  simpl.
  right. split.
  - unfold not. intros His_valid.
    destruct His_valid as [Hdigits Hex].
    destruct Hex as [prefix [suffix Hrest]].
    destruct Hrest as [Heq Hrest2].
    destruct Hrest2 as [HnoDot Hrest3].
    destruct Hrest3 as [HexFirstChar HsufAllowed].
    destruct HexFirstChar as [first_char [rest_prefix [Hpref Halpha]]].
    rewrite Hpref in Heq.
    revert Heq.
    vm_compute.
    intro Heq.
    inversion Heq; subst.
    unfold is_alpha in Halpha.
    destruct Halpha as [[Hbad _] | [Hbad _]]; vm_compute in Hbad; lia.
  - reflexivity.
Qed.