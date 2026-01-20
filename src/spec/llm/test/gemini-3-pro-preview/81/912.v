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
    [3.0; 2.7; 1.2; 2.8759777934749753; 2.5; 3.03614602926769; 3.8; 0.0; 2.2; 0.7; 1.7; 2.7; 3.5; 2.8; 0.5; 4.0; 1.1; 0.7378198540433399; 1.5; 1.5] 
    ["B"; "B-"; "D+"; "B"; "B-"; "B+"; "A"; "E"; "C+"; "D-"; "C-"; "B-"; "A-"; "B"; "D-"; "A+"; "D+"; "D"; "C-"; "C-"].
Proof.
  unfold numerical_letter_grade_spec.
  (* 1. Element: 3.0 -> "B" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 4 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 2. Element: 2.7 -> "B-" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 3. Element: 1.2 -> "D+" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 9 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 4. Element: 2.8759777934749753 -> "B" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 4 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 5. Element: 2.5 -> "B-" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 6. Element: 3.03614602926769 -> "B+" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 3 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 7. Element: 3.8 -> "A" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 8. Element: 0.0 -> "E" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 12 right.
    split; [lra | reflexivity].
  }
  (* 9. Element: 2.2 -> "C+" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 6 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 10. Element: 0.7 -> "D-" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 11 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 11. Element: 1.7 -> "C-" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 8 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 12. Element: 2.7 -> "B-" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 13. Element: 3.5 -> "A-" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 2 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 14. Element: 2.8 -> "B" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 4 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 15. Element: 0.5 -> "D-" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 11 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 16. Element: 4.0 -> "A+" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    left.
    split; [lra | reflexivity].
  }
  (* 17. Element: 1.1 -> "D+" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 9 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 18. Element: 0.7378198540433399 -> "D" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 10 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 19. Element: 1.5 -> "C-" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 8 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 20. Element: 1.5 -> "C-" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 8 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* End of list *)
  constructor.
Qed.