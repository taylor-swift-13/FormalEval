
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition fix_spaces_spec (text result : string) : Prop :=
  let fix replace_consecutive_spaces (n : nat) (s : string) : string :=
      match n with
      | 0 => s
      | S n' =>
        replace_consecutive_spaces n' (String.replace (String.make n " " "") "-" s)
      end in
  let intermediate := 
    (* replace all occurrences of 3 or more consecutive spaces with "-" *)
    let fix aux (len : nat) (s : string) :=
      match len with
      | 0 | 1 | 2 => s
      | S len' => aux len' (String.replace (String.make (S (S len')) " " "") "-" s)
      end
    in aux (String.length text) text in
  result = String.replace " " "_" intermediate /\
  (* for all k > 2, no substring of k consecutive spaces remain in result *)
  (forall k : nat, k > 2 -> ~ String.contains_substring result (String.make k " ")) /\
  (* for all occurrences of 3 or more consecutive spaces in text replaced by "-" in result *)
  (forall k s1 s2,
      k > 2 ->
      text = s1 ++ (String.make k " ") ++ s2 ->
      (* in result, s1, then "-", then s2 with spaces replaced by underscores *)
      exists s2',
        result = (String.replace " " "_" s1) ++ "-" ++ s2') /\
  (* all single or double spaces replaced by underscore *)
  (forall s1 s2,
      text = s1 ++ " " ++ s2 ->
      result = (String.replace " " "_" text)).
