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
    [0.1; 0.2; 0.3; 0.6; 0.8; 1.2; 1.5; 3.0393262031459374; 1.8; 2.2; 2.7; 3.1; 3.4; 3.5; 3.6; 3.7; 3.8; 3.9; 4.0] 
    ["D-"; "D-"; "D-"; "D-"; "D"; "D+"; "C-"; "B+"; "C"; "C+"; "B-"; "B+"; "A-"; "A-"; "A-"; "A-"; "A"; "A"; "A+"].
Proof.
  unfold numerical_letter_grade_spec.
  constructor.
  { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor.
  { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor.
  { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor.
  { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor.
  { unfold to_letter_grade_spec. do 10 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor.
  { unfold to_letter_grade_spec. do 9 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor.
  { unfold to_letter_grade_spec. do 8 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor.
  { unfold to_letter_grade_spec. do 3 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor.
  { unfold to_letter_grade_spec. do 7 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor.
  { unfold to_letter_grade_spec. do 6 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor.
  { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor.
  { unfold to_letter_grade_spec. do 3 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor.
  { unfold to_letter_grade_spec. right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor.
  { unfold to_letter_grade_spec. right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor.
  { unfold to_letter_grade_spec. left. split; [lra | reflexivity]. }
  constructor.
Qed.