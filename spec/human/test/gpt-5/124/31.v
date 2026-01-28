Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

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

Definition nat_of_2_digits (c1 c2 : ascii) : option nat :=
  match (nat_of_digit c1, nat_of_digit c2) with
  | (Some d1, Some d2) => Some (10 * d1 + d2)
  | _ => None
  end.

Definition nat_of_4_digits (c1 c2 c3 c4 : ascii) : option nat :=
  match (nat_of_digit c1, nat_of_digit c2, nat_of_digit c3, nat_of_digit c4) with
  | (Some d1, Some d2, Some d3, Some d4) => Some (1000 * d1 + 100 * d2 + 10 * d3 + d4)
  | _ => None
  end.

Definition days_in_month (m : nat) : nat :=
  match m with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | 2 => 29
  | _ => 0
  end.

Definition problem_124_pre (s : list ascii) : Prop := True.

Definition problem_124_spec (s : string) : Prop :=
  match list_ascii_of_string s with
  | [m1; m2; sep1; d1; d2; sep2; y1; y2; y3; y4] =>
      sep1 = "-"%char /\ sep2 = "-"%char /\
      (exists m d y,
        nat_of_2_digits m1 m2 = Some m /\
        nat_of_2_digits d1 d2 = Some d /\
        nat_of_4_digits y1 y2 y3 y4 = Some y /\
        (1 <= m <= 12 /\
         1 <= d <= days_in_month m))
  | _ => False
  end.

Example invalid_date_01_32_20000 : not (problem_124_spec "01-32-20000"%string).
Proof.
  unfold problem_124_spec.
  simpl.
  intros H.
  exact H.
Qed.