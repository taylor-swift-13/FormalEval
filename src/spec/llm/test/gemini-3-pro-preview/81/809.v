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
    [2.3034637938752276; 1.4916045811788032; 1.5; 2.0; 2.5; 2.347638745339878; 3.0; 3.0; 1.66650216124391; 1.5; 1.4916045811788032; 1.4916045811788032] 
    ["B-"; "C-"; "C-"; "C"; "B-"; "B-"; "B"; "B"; "C-"; "C-"; "C-"; "C-"].
Proof.
  unfold numerical_letter_grade_spec.
  (* 1. 2.303... -> B- *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 2. 1.491... -> C- *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 8 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 3. 1.5 -> C- *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 8 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 4. 2.0 -> C *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 7 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 5. 2.5 -> B- *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 6. 2.347... -> B- *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 7. 3.0 -> B *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 4 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 8. 3.0 -> B *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 4 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 9. 1.666... -> C- *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 8 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 10. 1.5 -> C- *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 8 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 11. 1.491... -> C- *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 8 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 12. 1.491... -> C- *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 8 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
Qed.