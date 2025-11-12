
Require Import Coq.Reals.Reals.
Require Import List.

Definition to_letter_grade_spec (score : R) (grade : string) : Prop :=
  (score = 4.0 -> grade = "A+") /\
  (score > 3.7 /\ score < 4.0 -> grade = "A") /\
  (score > 3.3 /\ score <= 3.7 -> grade = "A-") /\
  (score > 3.0 /\ score <= 3.3 -> grade = "B+") /\
  (score > 2.7 /\ score <= 3.0 -> grade = "B") /\
  (score > 2.3 /\ score <= 2.7 -> grade = "B-") /\
  (score > 2.0 /\ score <= 2.3 -> grade = "C+") /\
  (score > 1.7 /\ score <= 2.0 -> grade = "C") /\
  (score > 1.3 /\ score <= 1.7 -> grade = "C-") /\
  (score > 1.0 /\ score <= 1.3 -> grade = "D+") /\
  (score > 0.7 /\ score <= 1.0 -> grade = "D") /\
  (score > 0.0 /\ score <= 0.7 -> grade = "D-") /\
  (score <= 0.0 -> grade = "E").

Definition numerical_letter_grade_spec (grades : list R) (result : list string) : Prop :=
  Forall2 to_letter_grade_spec grades result.
