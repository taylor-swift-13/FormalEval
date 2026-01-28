Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.

Open Scope R_scope.
Open Scope string_scope.

Definition grade_relation (gpa : R) (grade : string) : Prop :=
  (gpa = 4.0 /\ grade = "A+") \/
  (3.7 < gpa /\ gpa < 4.0 /\ grade = "A") \/
  (3.3 < gpa /\ gpa <= 3.7 /\ grade = "A-") \/
  (3.0 < gpa /\ gpa <= 3.3 /\ grade = "B+") \/
  (2.7 < gpa /\ gpa <= 3.0 /\ grade = "B") \/
  (2.3 < gpa /\ gpa <= 2.7 /\ grade = "B-") \/
  (2.0 < gpa /\ gpa <= 2.3 /\ grade = "C+") \/
  (1.7 < gpa /\ gpa <= 2.0 /\ grade = "C") \/
  (1.3 < gpa /\ gpa <= 1.7 /\ grade = "C-") \/
  (1.0 < gpa /\ gpa <= 1.3 /\ grade = "D+") \/
  (0.7 < gpa /\ gpa <= 1.0 /\ grade = "D") \/
  (0.0 < gpa /\ gpa <= 0.7 /\ grade = "D-") \/
  (gpa = 0.0 /\ grade = "E").

Definition problem_81_pre (gpas : list R) : Prop :=
  Forall (fun g => 0 <= g /\ g <= 4) gpas.

Definition problem_81_spec (gpas : list R) (grades : list string) : Prop :=
  Forall2 grade_relation gpas grades.

Example problem_81_test :
  problem_81_spec [4.0; 3.5182986408219863; 3.9; 3.8; 3.7; 3.31; 2.2; 3.0; 2.99; 2.7; 2.69; 2.3; 0.8; 2.29; 2.0; 1.99; 1.7; 1.69; 1.3; 1.29; 0.7; 0.69; 0.0; 3.8] ["A+"; "A-"; "A"; "A"; "A-"; "A-"; "C+"; "B"; "B"; "B-"; "B-"; "C+"; "D"; "C+"; "C"; "C"; "C-"; "C-"; "D+"; "D+"; "D-"; "D-"; "E"; "A"].
Proof.
  unfold problem_81_spec.
  repeat (apply Forall2_cons; [unfold grade_relation; 
    first [ left; split; reflexivity
          | right; left; split; [lra | split; [lra | reflexivity]]
          | right; right; left; split; [lra | split; [lra | reflexivity]]
          | right; right; right; left; split; [lra | split; [lra | reflexivity]]
          | right; right; right; right; left; split; [lra | split; [lra | reflexivity]]
          | right; right; right; right; right; left; split; [lra | split; [lra | reflexivity]]
          | right; right; right; right; right; right; left; split; [lra | split; [lra | reflexivity]]
          | right; right; right; right; right; right; right; left; split; [lra | split; [lra | reflexivity]]
          | right; right; right; right; right; right; right; right; left; split; [lra | split; [lra | reflexivity]]
          | right; right; right; right; right; right; right; right; right; left; split; [lra | split; [lra | reflexivity]]
          | right; right; right; right; right; right; right; right; right; right; left; split; [lra | split; [lra | reflexivity]]
          | right; right; right; right; right; right; right; right; right; right; right; left; split; [lra | split; [lra | reflexivity]]
          | right; right; right; right; right; right; right; right; right; right; right; right; split; reflexivity
          ] | ]).
  apply Forall2_nil.
Qed.