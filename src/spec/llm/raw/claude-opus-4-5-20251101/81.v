
Require Import Coq.Reals.Reals.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope R_scope.

Definition to_letter_grade (score : R) : string :=
  if Req_dec score 4.0 then "A+"
  else if Rlt_dec 3.7 score then "A"
  else if Rlt_dec 3.3 score then "A-"
  else if Rlt_dec 3.0 score then "B+"
  else if Rlt_dec 2.7 score then "B"
  else if Rlt_dec 2.3 score then "B-"
  else if Rlt_dec 2.0 score then "C+"
  else if Rlt_dec 1.7 score then "C"
  else if Rlt_dec 1.3 score then "C-"
  else if Rlt_dec 1.0 score then "D+"
  else if Rlt_dec 0.7 score then "D"
  else if Rlt_dec 0.0 score then "D-"
  else "E".

Definition numerical_letter_grade_spec (grades : list R) (result : list string) : Prop :=
  result = map to_letter_grade grades.
