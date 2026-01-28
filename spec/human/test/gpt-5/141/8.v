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

Example problem_141_test_aREYA_exe :
  problem_141_spec "?aREYA.exe"%string "No"%string.
Proof.
  unfold problem_141_spec.
  simpl.
  right. split.
  - unfold not. intros His_valid.
    destruct His_valid as [Hdigits Hex].
    destruct Hex as [prefix [suffix [Heq [Hnodot [Hexfirst Hsuf]]]]].
    destruct Hexfirst as [first_char [rest_prefix [Hpref Healpha]]].
    rewrite Hpref in Heq.
    simpl in Heq.
    inversion Heq; subst.
    unfold is_alpha in Healpha.
    destruct Healpha as [[Hlower Hupper] | [HAlower HAupper]].
    + vm_compute in Hlower. lia.
    + vm_compute in HAlower. lia.
  - reflexivity.
Qed.