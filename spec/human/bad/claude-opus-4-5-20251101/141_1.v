Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Import Nat.

Definition is_digit_bool (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (nat_of_ascii "0" <=? n) && (n <=? nat_of_ascii "9").

Definition is_alpha (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (nat_of_ascii "a" <= n /\ n <= nat_of_ascii "z") \/
  (nat_of_ascii "A" <= n /\ n <= nat_of_ascii "Z").

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
      (suffix = ["t"; "x"; "t"]%char \/
       suffix = ["e"; "x"; "e"]%char \/
       suffix = ["d"; "l"; "l"]%char))
  in
  (is_valid /\ result = "Yes"%string) \/
  (~is_valid /\ result = "No"%string).

Example test_file_name_check_1 : problem_141_spec "example.txt"%string "Yes"%string.
Proof.
  unfold problem_141_spec.
  left.
  split.
  - split.
    + simpl. lia.
    + exists ["e"; "x"; "a"; "m"; "p"; "l"; "e"]%char.
      exists ["t"; "x"; "t"]%char.
      split.
      * simpl. reflexivity.
      * split.
        -- simpl. 
           intros H.
           destruct H as [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]];
           discriminate H.
        -- split.
           ++ exists "e"%char, ["x"; "a"; "m"; "p"; "l"; "e"]%char.
              split.
              ** reflexivity.
              ** unfold is_alpha. simpl.
                 left. split; lia.
           ++ left. reflexivity.
  - reflexivity.
Qed.