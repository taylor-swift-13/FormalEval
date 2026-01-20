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
    [3.419989154143125; 3.9; 3.8; 3.7; 3.31; 3.0; 2.99; 2.69; 2.3; 2.29; 1.030006862889675; 2.0; 1.99; 1.7; 1.3; 2.998584120230233; 1.29; 0.7; 0.69; 3.29; 1.7; 2.998584120230233] 
    ["A-"; "A"; "A"; "A-"; "A-"; "B"; "B"; "B-"; "C+"; "C+"; "D+"; "C"; "C"; "C-"; "D+"; "B"; "D+"; "D-"; "D-"; "B+"; "C-"; "B"].
Proof.
  unfold numerical_letter_grade_spec.
  (* 1. 3.419... -> A- *)
  constructor.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 2. 3.9 -> A *)
  constructor.
  { unfold to_letter_grade_spec. right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 3. 3.8 -> A *)
  constructor.
  { unfold to_letter_grade_spec. right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 4. 3.7 -> A- *)
  constructor.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 5. 3.31 -> A- *)
  constructor.
  { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 6. 3.0 -> B *)
  constructor.
  { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 7. 2.99 -> B *)
  constructor.
  { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 8. 2.69 -> B- *)
  constructor.
  { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 9. 2.3 -> C+ *)
  constructor.
  { unfold to_letter_grade_spec. do 6 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 10. 2.29 -> C+ *)
  constructor.
  { unfold to_letter_grade_spec. do 6 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 11. 1.03... -> D+ *)
  constructor.
  { unfold to_letter_grade_spec. do 9 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 12. 2.0 -> C *)
  constructor.
  { unfold to_letter_grade_spec. do 7 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 13. 1.99 -> C *)
  constructor.
  { unfold to_letter_grade_spec. do 7 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 14. 1.7 -> C- *)
  constructor.
  { unfold to_letter_grade_spec. do 8 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 15. 1.3 -> D+ *)
  constructor.
  { unfold to_letter_grade_spec. do 9 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 16. 2.998... -> B *)
  constructor.
  { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 17. 1.29 -> D+ *)
  constructor.
  { unfold to_letter_grade_spec. do 9 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 18. 0.7 -> D- *)
  constructor.
  { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 19. 0.69 -> D- *)
  constructor.
  { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 20. 3.29 -> B+ *)
  constructor.
  { unfold to_letter_grade_spec. do 3 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 21. 1.7 -> C- *)
  constructor.
  { unfold to_letter_grade_spec. do 8 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 22. 2.998... -> B *)
  constructor.
  { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }
  constructor.
Qed.