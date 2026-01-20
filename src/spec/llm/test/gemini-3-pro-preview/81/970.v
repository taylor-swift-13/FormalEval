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
    [2.7; 1.2; 2.5; 1.9179639623568823; 0.0; 0.7; 0.01985517592319941; 1.9; 3.5; 2.8; 0.7335880754647408; 0.8662047729715556; 1.1; 0.5902848664020242; 0.6813186450656247; 0.5481291210226951; 1.5; 1.7; 1.9179639623568823]
    ["B-"; "D+"; "B-"; "C"; "E"; "D-"; "D-"; "C"; "A-"; "B"; "D"; "D"; "D+"; "D-"; "D-"; "D-"; "C-"; "C-"; "C"].
Proof.
  unfold numerical_letter_grade_spec.
  (* 1. 2.7 -> B- *)
  constructor. { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 2. 1.2 -> D+ *)
  constructor. { unfold to_letter_grade_spec. do 9 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 3. 2.5 -> B- *)
  constructor. { unfold to_letter_grade_spec. do 5 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 4. 1.91... -> C *)
  constructor. { unfold to_letter_grade_spec. do 7 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 5. 0.0 -> E *)
  constructor. { unfold to_letter_grade_spec. do 12 right. split; [lra | reflexivity]. }
  (* 6. 0.7 -> D- *)
  constructor. { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 7. 0.019... -> D- *)
  constructor. { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 8. 1.9 -> C *)
  constructor. { unfold to_letter_grade_spec. do 7 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 9. 3.5 -> A- *)
  constructor. { unfold to_letter_grade_spec. do 2 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 10. 2.8 -> B *)
  constructor. { unfold to_letter_grade_spec. do 4 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 11. 0.73... -> D *)
  constructor. { unfold to_letter_grade_spec. do 10 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 12. 0.86... -> D *)
  constructor. { unfold to_letter_grade_spec. do 10 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 13. 1.1 -> D+ *)
  constructor. { unfold to_letter_grade_spec. do 9 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 14. 0.59... -> D- *)
  constructor. { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 15. 0.68... -> D- *)
  constructor. { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 16. 0.54... -> D- *)
  constructor. { unfold to_letter_grade_spec. do 11 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 17. 1.5 -> C- *)
  constructor. { unfold to_letter_grade_spec. do 8 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 18. 1.7 -> C- *)
  constructor. { unfold to_letter_grade_spec. do 8 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* 19. 1.91... -> C *)
  constructor. { unfold to_letter_grade_spec. do 7 right. left. split; [lra | split; [lra | reflexivity]]. }
  (* End *)
  constructor.
Qed.