
Require Import List.
Require Import String.
Require Import ZArith.
Open Scope string_scope.

Definition to_letter_grade_spec (score : Z) (grade : string) : Prop :=
  (score = 40 /\ grade = "A+") \/
  (37 < score < 40 /\ grade = "A") \/
  (33 < score <= 37 /\ grade = "A-") \/
  (30 < score <= 33 /\ grade = "B+") \/
  (27 < score <= 30 /\ grade = "B") \/
  (23 < score <= 27 /\ grade = "B-") \/
  (20 < score <= 23 /\ grade = "C+") \/
  (17 < score <= 20 /\ grade = "C") \/
  (13 < score <= 17 /\ grade = "C-") \/
  (10 < score <= 13 /\ grade = "D+") \/
  (7 < score <= 10 /\ grade = "D") \/
  (0 < score <= 7 /\ grade = "D-") \/
  (score = 0 /\ grade = "E").

Definition numerical_letter_grade_spec (grades : list Z) (letter_grades : list string) : Prop :=
  Forall2 to_letter_grade_spec grades letter_grades.
