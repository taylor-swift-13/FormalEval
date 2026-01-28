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
    [(27/10)%R; (12/10)%R; (25/10)%R; (29042970164851347/10000000000000000)%R; (19179639623568823/10000000000000000)%R; 0%R; (22/10)%R; (7/10)%R; (870282952445668/1000000000000000)%R; (19/10)%R; (35/10)%R; (28/10)%R; (7335880754647408/10000000000000000)%R; (8662047729715556/10000000000000000)%R; (11/10)%R; (5481291210226951/10000000000000000)%R; (15/10)%R; (17/10)%R; (28/10)%R; 0%R] 
    ["B-"; "D+"; "B-"; "B"; "C"; "E"; "C+"; "D-"; "D"; "C"; "A-"; "B"; "D"; "D"; "D+"; "D-"; "C-"; "C-"; "B"; "E"].
Proof.
  unfold numerical_letter_grade_spec.
  
  (* 1. 2.7 -> B- *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 2. 1.2 -> D+ *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 9 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 3. 2.5 -> B- *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 4. 2.904... -> B *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 4 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 5. 1.917... -> C *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 7 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 6. 0.0 -> E *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 12 right.
    split; [lra | reflexivity].
  }

  (* 7. 2.2 -> C+ *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 6 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 8. 0.7 -> D- *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 11 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 9. 0.870... -> D *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 10 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 10. 1.9 -> C *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 7 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 11. 3.5 -> A- *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 2 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 12. 2.8 -> B *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 4 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 13. 0.733... -> D *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 10 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 14. 0.866... -> D *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 10 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 15. 1.1 -> D+ *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 9 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 16. 0.548... -> D- *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 11 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 17. 1.5 -> C- *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 8 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 18. 1.7 -> C- *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 8 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 19. 2.8 -> B *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 4 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 20. 0.0 -> E *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 12 right.
    split; [lra | reflexivity].
  }

  (* End of list *)
  apply Forall2_nil.
Qed.