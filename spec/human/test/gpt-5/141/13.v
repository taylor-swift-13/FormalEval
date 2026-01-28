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

Example problem_141_test_hash_this2_i4s_5valid_ten :
  problem_141_spec "#this2_i4s_5valid.ten"%string "No"%string.
Proof.
  unfold problem_141_spec.
  simpl.
  right. split.
  - intros [Hdigits [prefix [suffix [Heq [HnoDot [HstartAlpha Hsuf]]]]]].
    destruct prefix as [|p0 pr].
    + vm_compute in Heq. discriminate.
    + vm_compute in Heq. inversion Heq; subst p0.
      destruct HstartAlpha as [first_char [rest_prefix [HprefEq Halpha]]].
      inversion HprefEq; subst first_char rest_prefix.
      unfold is_alpha in Halpha.
      destruct Halpha as [[Ha1 _] | [Ha1 _]]; vm_compute in Ha1; lia.
  - reflexivity.
Qed.