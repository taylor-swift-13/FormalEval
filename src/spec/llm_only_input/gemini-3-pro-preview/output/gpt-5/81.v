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
    [4.0%R; 3%R; 1.7%R; 2%R; 3.5%R]
    ["A+"; "B"; "C-"; "C"; "A-"].
Proof.
  unfold numerical_letter_grade_spec.
  (* Case 1: 4.0 -> A+ *)
  constructor.
  {
    unfold to_letter_grade_spec.
    left.
    split; [lra | reflexivity].
  }
  (* Case 2: 3.0 -> B *)
  constructor.
  {
    unfold to_letter_grade_spec.
    (* Skip A+, A, A-, B+ to reach B *)
    right. right. right. right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* Case 3: 1.7 -> C- *)
  constructor.
  {
    unfold to_letter_grade_spec.
    (* Skip A+ through C to reach C- (9th clause) *)
    do 8 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* Case 4: 2.0 -> C *)
  constructor.
  {
    unfold to_letter_grade_spec.
    (* Skip A+ through C+ to reach C (8th clause) *)
    do 7 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* Case 5: 3.5 -> A- *)
  constructor.
  {
    unfold to_letter_grade_spec.
    (* Skip A+, A to reach A- (3rd clause) *)
    right. right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  (* End of list *)
  constructor.
Qed.