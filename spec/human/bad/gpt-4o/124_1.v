Here's the corrected Coq proof:

```coq
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(* Auxiliary function: Convert a digit character to a nat *)
Definition nat_of_digit (c : ascii) : option nat :=
  match c with
  | "0"%char => Some 0
  | "1"%char => Some 1
  | "2"%char => Some 2
  | "3"%char => Some 3
  | "4"%char => Some 4
  | "5"%char => Some 5
  | "6"%char => Some 6
  | "7"%char => Some 7
  | "8"%char => Some 8
  | "9"%char => Some 9
  | _ => None
  end.

(* Auxiliary function: Convert two digit characters to a nat *)
Definition nat_of_2_digits (c1 c2 : ascii) : option nat :=
  match (nat_of_digit c1, nat_of_digit c2) with
  | (Some d1, Some d2) => Some (10 * d1 + d2)
  | _ => None
  end.

(* Auxiliary function: Convert four digit characters to a nat *)
Definition nat_of_4_digits (c1 c2 c3 c4 : ascii) : option nat :=
  match (nat_of_digit c1, nat_of_digit c2, nat_of_digit c3, nat_of_digit c4) with
  | (Some d1, Some d2, Some d3, Some d4) => Some (1000 * d1 + 100 * d2 + 10 * d3 + d4)
  | _ => None
  end.

(* Auxiliary function: Get the maximum days for a given month *)
Definition days_in_month (m : nat) : nat :=
  match m with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | 2 => 29 (* Based on rule #2 *)
  | _ => 0 (* Invalid month *)
  end.

(* As a validation function, input can be any list of characters *)
Definition problem_124_pre (s : list ascii) : Prop := True.

(* Specification: This Prop defines that the input character list s is valid if it satisfies all date rules *)
Definition problem_124_spec (s : string) : Prop :=
  match list_ascii_of_string s with
  (* Pattern match the "mm-dd-yyyy" format, implicitly checking the list length is 10 *)
  | [m1; m2; sep1; d1; d2; sep2; y1; y2; y3; y4] =>
      (* 1. Check separators are '-' *)
      sep1 = "-"%char /\ sep2 = "-"%char /\
      (* Try parsing characters as month, day, year *)
      (exists m d y,
        nat_of_2_digits m1 m2 = Some m /\
        nat_of_2_digits d1 d2 = Some d /\
        nat_of_4_digits y1 y2 y3 y4 = Some y /\
        (* 2. Check month range (1-12) *)
        (1 <= m <= 12 /\
        (* 3. Check day range (1 to max days of the month) *)
         1 <= d <= days_in_month m))
  (* If the character list doesn't match the 10 character format, it's invalid *)
  | _ => False
  end.

(* Test case *)
Example test_case_1 : problem_124_spec "03-11-2000".
Proof.
  unfold problem_124_spec.
  simpl.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + exists 3, 11, 2000.
      split.
      * reflexivity.
      * split.
        -- reflexivity.
        -- split.
           ++ reflexivity.
           ++ split.
              ** apply Nat.le_refl. (* 1 <= 3 is true because 3 >= 1 *)
              ** apply Nat.le_refl. (* 11 <= 31 is true because 11 <= 31 *)
Qed.