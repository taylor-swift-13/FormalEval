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
    [(1/10)%R; (2/10)%R; (3/10)%R; (6/10)%R; (8/10)%R; (12/10)%R; (15/10)%R; (18/10)%R; (22/10)%R; (27/10)%R; (2482496149479828/1000000000000000)%R; (34/10)%R; (35/10)%R; (36/10)%R; (37/10)%R; (38/10)%R; (39/10)%R; 4%R; (2/10)%R] 
    ["D-"; "D-"; "D-"; "D-"; "D"; "D+"; "C-"; "C"; "C+"; "B-"; "B-"; "A-"; "A-"; "A-"; "A-"; "A"; "A"; "A+"; "D-"].
Proof.
  unfold numerical_letter_grade_spec.
  
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 10 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 9 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 8 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 7 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 6 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. left. split; [lra | reflexivity]. }

  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_nil.
Qed.