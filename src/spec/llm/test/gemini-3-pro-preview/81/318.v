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
    [3.9; 3.8; 3.7; 3.0119324827406504; 3.5; 3.4; 3.3; 3.5; 3.1; 2.9264230458450027; 2.9; 2.6; 2.5; 2.4; 2.3; 2.189704692581822; 2.1; 2.9960109163522706; 2.1; 2.6; 3.7] 
    ["A"; "A"; "A-"; "B+"; "A-"; "A-"; "B+"; "A-"; "B+"; "B"; "B"; "B-"; "B-"; "B-"; "C+"; "C+"; "C+"; "B"; "C+"; "B-"; "A-"].
Proof.
  unfold numerical_letter_grade_spec.
  constructor.
  { (* 3.9 -> A *)
    unfold to_letter_grade_spec.
    right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  { (* 3.8 -> A *)
    unfold to_letter_grade_spec.
    right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  { (* 3.7 -> A- *)
    unfold to_letter_grade_spec.
    do 2 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  { (* 3.0119324827406504 -> B+ *)
    unfold to_letter_grade_spec.
    do 3 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  { (* 3.5 -> A- *)
    unfold to_letter_grade_spec.
    do 2 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  { (* 3.4 -> A- *)
    unfold to_letter_grade_spec.
    do 2 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  { (* 3.3 -> B+ *)
    unfold to_letter_grade_spec.
    do 3 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  { (* 3.5 -> A- *)
    unfold to_letter_grade_spec.
    do 2 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  { (* 3.1 -> B+ *)
    unfold to_letter_grade_spec.
    do 3 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  { (* 2.9264230458450027 -> B *)
    unfold to_letter_grade_spec.
    do 4 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  { (* 2.9 -> B *)
    unfold to_letter_grade_spec.
    do 4 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  { (* 2.6 -> B- *)
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  { (* 2.5 -> B- *)
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  { (* 2.4 -> B- *)
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  { (* 2.3 -> C+ *)
    unfold to_letter_grade_spec.
    do 6 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  { (* 2.189704692581822 -> C+ *)
    unfold to_letter_grade_spec.
    do 6 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  { (* 2.1 -> C+ *)
    unfold to_letter_grade_spec.
    do 6 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  { (* 2.9960109163522706 -> B *)
    unfold to_letter_grade_spec.
    do 4 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  { (* 2.1 -> C+ *)
    unfold to_letter_grade_spec.
    do 6 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  { (* 2.6 -> B- *)
    unfold to_letter_grade_spec.
    do 5 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
  { (* 3.7 -> A- *)
    unfold to_letter_grade_spec.
    do 2 right. left.
    split; [lra | split; [lra | reflexivity]].
  }
  constructor.
Qed.