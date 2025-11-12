
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Import ListNotations.

Definition letter_grade := string.

Definition numerical_letter_grade_spec (grades : list R) (letters : list letter_grade) : Prop :=
  length grades = length letters /\
  forall i grade letter,
    nth_error grades i = Some grade ->
    nth_error letters i = Some letter ->
    (   (grade = 4.0 /\ letter = "A+")
     \/ (grade > 3.7 /\ grade < 4.0 /\ letter = "A")
     \/ (grade > 3.3 /\ grade <= 3.7 /\ letter = "A-")
     \/ (grade > 3.0 /\ grade <= 3.3 /\ letter = "B+")
     \/ (grade > 2.7 /\ grade <= 3.0 /\ letter = "B")
     \/ (grade > 2.3 /\ grade <= 2.7 /\ letter = "B-")
     \/ (grade > 2.0 /\ grade <= 2.3 /\ letter = "C+")
     \/ (grade > 1.7 /\ grade <= 2.0 /\ letter = "C")
     \/ (grade > 1.3 /\ grade <= 1.7 /\ letter = "C-")
     \/ (grade > 1.0 /\ grade <= 1.3 /\ letter = "D+")
     \/ (grade > 0.7 /\ grade <= 1.0 /\ letter = "D")
     \/ (grade > 0.0 /\ grade <= 0.7 /\ letter = "D-")
     \/ (grade = 0.0 /\ letter = "E")
     \/ (grade < 0.0 /\ letter = "E") ). 
