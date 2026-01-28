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
    [4%R; (39/10)%R; (38/10)%R; (37/10)%R; (331/100)%R; (329/100)%R; 3%R; (299/100)%R; (27/10)%R; (23/10)%R; (229/100)%R; 2%R; (199/100)%R; (17/10)%R; (169/100)%R; (13/10)%R; (129/100)%R; (7/10)%R; (69/100)%R; 0%R; (329/100)%R] 
    ["A+"; "A"; "A"; "A-"; "A-"; "B+"; "B"; "B"; "B-"; "C+"; "C+"; "C"; "C"; "C-"; "C-"; "D+"; "D+"; "D-"; "D-"; "E"; "B+"].
Proof.
  unfold numerical_letter_grade_spec.
  
  (* 1. 4.0 -> A+ *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. left. split; [lra | reflexivity]. }

  (* 2. 3.9 -> A *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 3. 3.8 -> A *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 4. 3.7 -> A- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 5. 3.31 -> A- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 6. 3.29 -> B+ *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 3 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 7. 3.0 -> B *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 8. 2.99 -> B *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 9. 2.7 -> B- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 10. 2.3 -> C+ *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 6 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 11. 2.29 -> C+ *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 6 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 12. 2.0 -> C *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 7 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 13. 1.99 -> C *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 7 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 14. 1.7 -> C- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 8 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 15. 1.69 -> C- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 8 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 16. 1.3 -> D+ *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 9 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 17. 1.29 -> D+ *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 9 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 18. 0.7 -> D- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 19. 0.69 -> D- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 20. 0.0 -> E *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 12 right. split; [lra | reflexivity]. }

  (* 21. 3.29 -> B+ *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 3 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_nil.
Qed.