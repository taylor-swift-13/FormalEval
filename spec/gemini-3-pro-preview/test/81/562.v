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
    [3.0; 2.7; 0.8808755499445509; 2.5; 3.9; 2.9; 3.8; 3.8; 2.2; 0.7; 2.6725566512853307; 3.121783346183994; 2.8; 1.1; 1.5; 1.1; 3.121783346183994; 2.9]
    ["B"; "B-"; "D"; "B-"; "A"; "B"; "A"; "A"; "C+"; "D-"; "B-"; "B+"; "B"; "D+"; "C-"; "D+"; "B+"; "B"].
Proof.
  unfold numerical_letter_grade_spec.
  (* 1. 3.0 -> B *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 4 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 2. 2.7 -> B- *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 3. 0.88... -> D *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 10 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 4. 2.5 -> B- *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 5. 3.9 -> A *)
  constructor.
  {
    unfold to_letter_grade_spec.
    right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 6. 2.9 -> B *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 4 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 7. 3.8 -> A *)
  constructor.
  {
    unfold to_letter_grade_spec.
    right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 8. 3.8 -> A *)
  constructor.
  {
    unfold to_letter_grade_spec.
    right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 9. 2.2 -> C+ *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 6 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 10. 0.7 -> D- *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 11 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 11. 2.67... -> B- *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 12. 3.12... -> B+ *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 3 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 13. 2.8 -> B *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 4 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 14. 1.1 -> D+ *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 9 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 15. 1.5 -> C- *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 8 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 16. 1.1 -> D+ *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 9 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 17. 3.12... -> B+ *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 3 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 18. 2.9 -> B *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 4 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
Qed.