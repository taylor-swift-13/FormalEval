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
    [3%R; (37/10)%R; (33/10)%R; (3235565911123312/1000000000000000)%R; 2%R; (13077251960091935/100000000000000000)%R; (27/10)%R; (23/10)%R; 1%R; (17/10)%R; (13/10)%R; 0%R; (37420880401780154/100000000000000000)%R; (7/10)%R; (23158336467557668/10000000000000000)%R; 4%R; (22000284044866794/10000000000000000)%R; (1/10)%R; (15/10)%R; (35/10)%R; (28/10)%R; (22000284044866794/10000000000000000)%R; (2993721077381442/1000000000000000)%R; (17/10)%R] 
    ["B"; "A-"; "B+"; "B+"; "C"; "D-"; "B-"; "C+"; "D"; "C-"; "D+"; "E"; "D-"; "D-"; "B-"; "A+"; "C+"; "D-"; "C-"; "A-"; "B"; "C+"; "B"; "C-"].
Proof.
  unfold numerical_letter_grade_spec.

  (* 1. 3.0 -> B *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 2. 3.7 -> A- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 3. 3.3 -> B+ *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 3 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 4. 3.23... -> B+ *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 3 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 5. 2.0 -> C *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 7 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 6. 0.13... -> D- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 7. 2.7 -> B- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 8. 2.3 -> C+ *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 6 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 9. 1.0 -> D *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 10 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 10. 1.7 -> C- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 8 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 11. 1.3 -> D+ *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 9 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 12. 0 -> E *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 12 right. split; [lra | reflexivity]. }

  (* 13. 0.37... -> D- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 14. 0.7 -> D- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 15. 2.31... -> B- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 16. 4.0 -> A+ *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. left. split; [lra | reflexivity]. }

  (* 17. 2.20... -> C+ *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 6 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 18. 0.1 -> D- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 19. 1.5 -> C- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 8 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 20. 3.5 -> A- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 21. 2.8 -> B *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 22. 2.20... -> C+ *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 6 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 23. 2.99... -> B *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }

  (* 24. 1.7 -> C- *)
  apply Forall2_cons.
  { unfold to_letter_grade_spec. do 8 right. left. split; [lra | split; [lra | reflexivity]]. }

  apply Forall2_nil.
Qed.