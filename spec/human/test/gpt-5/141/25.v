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

Example problem_141_test_dot_txt :
  problem_141_spec ".txt"%string "No"%string.
Proof.
  unfold problem_141_spec.
  simpl.
  right. split.
  - unfold not. intros [Hdigits [prefix [suffix [Hconcat [Hnodot [Halpha Hsuf]]]]]].
    destruct prefix as [|p1 rest_prefix].
    + destruct Halpha as [first_char [rest [Hpref _]]]. inversion Hpref.
    + simpl in Hconcat. inversion Hconcat; subst.
      assert (In "."%char (((("."%char)::rest_prefix) ++ suffix))) as Hin.
      { apply in_or_app. left. simpl. left. reflexivity. }
      apply Hnodot in Hin. contradiction.
  - reflexivity.
Qed.