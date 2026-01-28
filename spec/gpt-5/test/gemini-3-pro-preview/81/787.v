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
    [3.6%R; 1.9%R; 2.7%R; 0.5%R; 3.8%R; 2.5%R; 3.9%R; 2.2%R; 1.1%R; 1.469249244129425%R; 3.3%R; 0.3%R; 2.5847832150444283%R; 3.0%R; 2.8%R; 2.1%R; 1.0974926345706222%R; 3.5%R; 3.2%R; 0.9%R; 2.5249306372830596%R; 0.8021147018594553%R; 2.2%R] 
    ["A-"; "C"; "B-"; "D-"; "A"; "B-"; "A"; "C+"; "D+"; "C-"; "B+"; "D-"; "B-"; "B"; "B"; "C+"; "D+"; "A-"; "B+"; "D"; "B-"; "D"; "C+"].
Proof.
  unfold numerical_letter_grade_spec.

  (* 1. 3.6 -> A- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 2. 1.9 -> C *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 7 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 3. 2.7 -> B- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 4. 0.5 -> D- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 5. 3.8 -> A *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 6. 2.5 -> B- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 7. 3.9 -> A *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 8. 2.2 -> C+ *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 6 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 9. 1.1 -> D+ *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 9 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 10. 1.469... -> C- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 8 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 11. 3.3 -> B+ *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 3 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 12. 0.3 -> D- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 13. 2.584... -> B- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 14. 3.0 -> B *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 15. 2.8 -> B *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 16. 2.1 -> C+ *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 6 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 17. 1.097... -> D+ *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 9 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 18. 3.5 -> A- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 19. 3.2 -> B+ *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 3 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 20. 0.9 -> D *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 10 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 21. 2.524... -> B- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 22. 0.802... -> D *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 10 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 23. 2.2 -> C+ *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 6 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_nil.
Qed.