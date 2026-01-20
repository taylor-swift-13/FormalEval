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
    [3.9; 3.7; 3.6; 3.5; 3.4; 3.3; 3.2; 3.1; 3.0; 2.9; 2.8; 2.7; 2.798786831409463; 2.5; 2.4; 4.0; 2.989123794765767; 2.2; 2.1; 2.7]
    ["A"; "A-"; "A-"; "A-"; "A-"; "B+"; "B+"; "B+"; "B"; "B"; "B"; "B-"; "B"; "B-"; "B-"; "A+"; "B"; "C+"; "C+"; "B-"].
Proof.
  unfold numerical_letter_grade_spec.
  (* 1. 3.9 -> A *)
  constructor.
  { unfold to_letter_grade_spec. right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 2. 3.7 -> A- *)
  constructor.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 3. 3.6 -> A- *)
  constructor.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 4. 3.5 -> A- *)
  constructor.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 5. 3.4 -> A- *)
  constructor.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 6. 3.3 -> B+ *)
  constructor.
  { unfold to_letter_grade_spec. do 3 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 7. 3.2 -> B+ *)
  constructor.
  { unfold to_letter_grade_spec. do 3 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 8. 3.1 -> B+ *)
  constructor.
  { unfold to_letter_grade_spec. do 3 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 9. 3.0 -> B *)
  constructor.
  { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 10. 2.9 -> B *)
  constructor.
  { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 11. 2.8 -> B *)
  constructor.
  { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 12. 2.7 -> B- *)
  constructor.
  { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 13. 2.798... -> B *)
  constructor.
  { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 14. 2.5 -> B- *)
  constructor.
  { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 15. 2.4 -> B- *)
  constructor.
  { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 16. 4.0 -> A+ *)
  constructor.
  { unfold to_letter_grade_spec. left. split; [lra | reflexivity]. }
  (* 17. 2.989... -> B *)
  constructor.
  { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 18. 2.2 -> C+ *)
  constructor.
  { unfold to_letter_grade_spec. do 6 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 19. 2.1 -> C+ *)
  constructor.
  { unfold to_letter_grade_spec. do 6 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 20. 2.7 -> B- *)
  constructor.
  { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor.
Qed.