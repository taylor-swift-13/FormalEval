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
    [4.0%R; 3.9%R; 3.8%R; 3.7%R; 3.31%R; 3.29%R; 3.1%R; 3.0%R; 2.9627589397420344%R; 2.7%R; 2.69%R; 2.29%R; 3.9%R; 2.0%R; 1.99%R; 1.7%R; 1.69%R; 1.69%R; 1.29%R; 3.0089656924915475%R; 0.7%R; 1.9179639623568823%R; 0.69%R; 0.0%R; 4.0%R] 
    ["A+"; "A"; "A"; "A-"; "A-"; "B+"; "B+"; "B"; "B"; "B-"; "B-"; "C+"; "A"; "C"; "C"; "C-"; "C-"; "C-"; "D+"; "B+"; "D-"; "C"; "D-"; "E"; "A+"].
Proof.
  unfold numerical_letter_grade_spec.

  (* 1. Score: 4.0 -> "A+" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    left.
    split; [lra | reflexivity].
  }

  (* 2. Score: 3.9 -> "A" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 3. Score: 3.8 -> "A" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 4. Score: 3.7 -> "A-" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 2 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 5. Score: 3.31 -> "A-" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 2 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 6. Score: 3.29 -> "B+" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 3 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 7. Score: 3.1 -> "B+" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 3 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 8. Score: 3.0 -> "B" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 4 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 9. Score: 2.9627589397420344 -> "B" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 4 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 10. Score: 2.7 -> "B-" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 11. Score: 2.69 -> "B-" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 12. Score: 2.29 -> "C+" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 6 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 13. Score: 3.9 -> "A" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 14. Score: 2.0 -> "C" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 7 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 15. Score: 1.99 -> "C" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 7 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 16. Score: 1.7 -> "C-" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 8 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 17. Score: 1.69 -> "C-" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 8 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 18. Score: 1.69 -> "C-" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 8 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 19. Score: 1.29 -> "D+" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 9 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 20. Score: 3.0089656924915475 -> "B+" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 3 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 21. Score: 0.7 -> "D-" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 11 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 22. Score: 1.9179639623568823 -> "C" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 7 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 23. Score: 0.69 -> "D-" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 11 right. left.
    split; [lra | split; [lra | reflexivity]].
  }

  (* 24. Score: 0.0 -> "E" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    do 12 right.
    split; [lra | reflexivity].
  }

  (* 25. Score: 4.0 -> "A+" *)
  apply Forall2_cons.
  {
    unfold to_letter_grade_spec.
    left.
    split; [lra | reflexivity].
  }

  (* End of list *)
  apply Forall2_nil.
Qed.