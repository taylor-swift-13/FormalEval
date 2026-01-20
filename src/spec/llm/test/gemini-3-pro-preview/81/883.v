Require Import Coq.Reals.Reals.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.
Open Scope string_scope.

Definition to_letter_grade_spec (score : R) (grade : string) : Prop :=
  (score = 4.0 /\ grade = "A+") \/
  (score <> 4.0 /\ score > 3.7 /\ grade = "A") \/
  (score <= 3.7 /\ score > 3.3 /\ grade = "A-") \/
  (score <= 3.3 /\ score > 3.0 /\ grade = "B+") \/
  (score <= 3.0 /\ score > 2.7 /\ grade = "B") \/
  (score <= 2.7 /\ score > 2.3 /\ grade = "B-") \/
  (score <= 2.3 /\ score > 2.0 /\ grade = "C+") \/
  (score <= 2.0 /\ score > 1.7 /\ grade = "C") \/
  (score <= 1.7 /\ score > 1.3 /\ grade = "C-") \/
  (score <= 1.3 /\ score > 1.0 /\ grade = "D+") \/
  (score <= 1.0 /\ score > 0.7 /\ grade = "D") \/
  (score <= 0.7 /\ score > 0.0 /\ grade = "D-") \/
  (score <= 0.0 /\ grade = "E").

Definition numerical_letter_grade_spec (grades : list R) (result : list string) : Prop :=
  Forall2 to_letter_grade_spec grades result.

Example test_numerical_letter_grade :
  numerical_letter_grade_spec 
    [3.9; 3.6759088043422827; 2.1003344731606215; 3.5; 3.4; 3.3; 3.2; 3.1; 3.0; 2.9; 2.8; 0.7; 2.019078867628035; 2.7; 2.6; 2.5; 3.5913526622381533; 2.4; 2.2615377417153852; 2.2; 2.1; 2.0; 2.2; 3.4] 
    ["A"; "A-"; "C+"; "A-"; "A-"; "B+"; "B+"; "B+"; "B"; "B"; "B"; "D-"; "C+"; "B-"; "B-"; "B-"; "A-"; "B-"; "C+"; "C+"; "C+"; "C"; "C+"; "A-"].
Proof.
  unfold numerical_letter_grade_spec.
  constructor.
  {
    unfold to_letter_grade_spec.
    do 1 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 2 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 6 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 2 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 2 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 3 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 3 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 3 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 4 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 4 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 4 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 11 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 6 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 2 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 6 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 6 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 6 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 7 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 6 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  {
    unfold to_letter_grade_spec.
    do 2 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
Qed.