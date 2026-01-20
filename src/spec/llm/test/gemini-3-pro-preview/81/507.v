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
    [1.9029418657170252; 3.5; 3.7; 3.3; 2.043633551545988; 2.3; 0.6481189062280039; 1.3; 1.2224601670126722; 0.5; 1.946120157163334; 2.3; 2.902011925364104; 2.043633551545988] 
    ["C"; "A-"; "A-"; "B+"; "C+"; "C+"; "D-"; "D+"; "D+"; "D-"; "C"; "C+"; "B"; "C+"].
Proof.
  unfold numerical_letter_grade_spec.
  (* 1. 1.90294... -> "C" (1.7 < x <= 2.0) *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 7 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 2. 3.5 -> "A-" (3.3 < x <= 3.7) *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 2 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 3. 3.7 -> "A-" (3.3 < x <= 3.7) *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 2 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 4. 3.3 -> "B+" (3.0 < x <= 3.3) *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 3 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 5. 2.04363... -> "C+" (2.0 < x <= 2.3) *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 6 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 6. 2.3 -> "C+" (2.0 < x <= 2.3) *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 6 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 7. 0.64811... -> "D-" (0.0 < x <= 0.7) *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 11 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 8. 1.3 -> "D+" (1.0 < x <= 1.3) *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 9 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 9. 1.22246... -> "D+" (1.0 < x <= 1.3) *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 9 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 10. 0.5 -> "D-" (0.0 < x <= 0.7) *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 11 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 11. 1.94612... -> "C" (1.7 < x <= 2.0) *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 7 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 12. 2.3 -> "C+" (2.0 < x <= 2.3) *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 6 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 13. 2.90201... -> "B" (2.7 < x <= 3.0) *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 4 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 14. 2.04363... -> "C+" (2.0 < x <= 2.3) *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 6 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* End of list *)
  constructor.
Qed.