Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lra.

Import ListNotations.

Open Scope R_scope.
Open Scope string_scope.

Definition to_letter_grade_spec (score : R) (letter : string) : Prop :=
  (score = 4%R /\ letter = "A+") \/
  ((37%R / 10%R) < score /\ score <> 4%R /\ letter = "A") \/
  ((33%R / 10%R) < score /\ score <= (37%R / 10%R) /\ letter = "A-") \/
  (3%R < score /\ score <= (33%R / 10%R) /\ letter = "B+") \/
  ((27%R / 10%R) < score /\ score <= 3%R /\ letter = "B") \/
  ((23%R / 10%R) < score /\ score <= (27%R / 10%R) /\ letter = "B-") \/
  (2%R < score /\ score <= (23%R / 10%R) /\ letter = "C+") \/
  ((17%R / 10%R) < score /\ score <= 2%R /\ letter = "C") \/
  ((13%R / 10%R) < score /\ score <= (17%R / 10%R) /\ letter = "C-") \/
  (1%R < score /\ score <= (13%R / 10%R) /\ letter = "D+") \/
  ((7%R / 10%R) < score /\ score <= 1%R /\ letter = "D") \/
  (0%R < score /\ score <= (7%R / 10%R) /\ letter = "D-") \/
  (score <= 0%R /\ letter = "E").

Definition numerical_letter_grade_spec (grades : list R) (letters : list string) : Prop :=
  Forall2 to_letter_grade_spec grades letters.

Example test_numerical_letter_grade : 
  numerical_letter_grade_spec 
    [2.1%R; 3.0%R; 2.29%R; 1.2%R; 2.5%R; 3.9%R; 2.9%R; 1.4717072828761908%R; 3.8%R; 3.8%R; 2.2%R; 0.7%R; 2.6123925604631633%R; 2.6725566512853307%R; 3.5%R; 2.8%R; 1.1%R; 3.8%R; 1.5%R; 3.9%R] 
    ["C+"; "B"; "C+"; "D+"; "B-"; "A"; "B"; "C-"; "A"; "A"; "C+"; "D-"; "B-"; "B-"; "A-"; "B"; "D+"; "A"; "C-"; "A"].
Proof.
  unfold numerical_letter_grade_spec.

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 6 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 6 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 9 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 8 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 6 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 9 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 8 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_nil.
Qed.