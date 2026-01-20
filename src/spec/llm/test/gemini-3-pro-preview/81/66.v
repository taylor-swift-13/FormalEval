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
  numerical_letter_grade_spec [3.2; 1.805599623539984; 1.607214262835292; 2.5; 1.0; 3.2; 1.0] ["B+"; "C"; "C-"; "B-"; "D"; "B+"; "D"].
Proof.
  unfold numerical_letter_grade_spec.
  (* 1. Element: 3.2 -> "B+" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 3 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 2. Element: 1.805599623539984 -> "C" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 7 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 3. Element: 1.607214262835292 -> "C-" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 8 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 4. Element: 2.5 -> "B-" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 5. Element: 1.0 -> "D" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 10 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 6. Element: 3.2 -> "B+" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 3 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* 7. Element: 1.0 -> "D" *)
  constructor.
  {
    unfold to_letter_grade_spec.
    do 10 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* End of list *)
  constructor.
Qed.