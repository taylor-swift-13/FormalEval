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
    [3.6; 1.9; 2.7; 1.29; 3.8; 1.6861731437934284; 3.9; 3.0577626154561717; 1.2141825320982542; 1.1; 3.3; 0.3; 3.0; 2.8; 1.7; 2.1; 1.6; 3.5; 3.2; 0.9; 2.6; 2.8; 1.29; 1.9]
    ["A-"; "C"; "B-"; "D+"; "A"; "C-"; "A"; "B+"; "D+"; "D+"; "B+"; "D-"; "B"; "B"; "C-"; "C+"; "C-"; "A-"; "B+"; "D"; "B-"; "B"; "D+"; "C"].
Proof.
  unfold numerical_letter_grade_spec.
  constructor. { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. do 7 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. do 9 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. do 8 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. do 3 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. do 9 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. do 9 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. do 3 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. do 8 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. do 6 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. do 8 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. do 3 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. do 10 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. do 9 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor. { unfold to_letter_grade_spec. do 7 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor.
Qed.