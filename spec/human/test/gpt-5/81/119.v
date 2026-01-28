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

Example numerical_letter_grade_example :
  problem_81_spec
    [4.0%R; 3.5182986408219863%R; 3.9%R; 3.8%R; 3.7%R; 3.31%R; 2.2%R; 3.0%R; 2.99%R; 2.7%R; 2.69%R; 2.3%R; 2.29%R; 2.0%R; 1.99%R; 1.7%R; 1.69%R; 1.3%R; 1.29%R; 0.7%R; 0.69%R; 0.0%R]
    ["A+"; "A-"; "A"; "A"; "A-"; "A-"; "C+"; "B"; "B"; "B-"; "B-"; "C+"; "C+"; "C"; "C"; "C-"; "C-"; "D+"; "D+"; "D-"; "D-"; "E"].
Proof.
  unfold problem_81_spec.
  apply Forall2_cons.
  - unfold grade_relation.
    left. split; reflexivity.
  - apply Forall2_cons.
    + unfold grade_relation.
      right; right; left.
      split.
      * lra.
      * split; [lra|reflexivity].
    + apply Forall2_cons.
      * unfold grade_relation.
        right; left.
        split.
        -- lra.
        -- split; [lra|reflexivity].
      * apply Forall2_cons.
        -- unfold grade_relation.
           right; left.
           split.
           ** lra.
           ** split; [lra|reflexivity].
        -- apply Forall2_cons.
           ++ unfold grade_relation.
              right; right; left.
              split.
              ** lra.
              ** split; [lra|reflexivity].
           ++ apply Forall2_cons.
              ** unfold grade_relation.
                 right; right; left.
                 split.
                 --- lra.
                 --- split; [lra|reflexivity].
              ** apply Forall2_cons.
                 --- unfold grade_relation.
                     right; right; right; right; right; right; left.
                     split.
                     **** lra.
                     **** split; [lra|reflexivity].
                 --- apply Forall2_cons.
                     **** unfold grade_relation.
                          right; right; right; right; left.
                          split.
                          ***** lra.
                          ***** split; [lra|reflexivity].
                     **** apply Forall2_cons.
                          ***** unfold grade_relation.
                                right; right; right; right; left.
                                split.
                                ****** lra.
                                ****** split; [lra|reflexivity].
                          ***** apply Forall2_cons.
                                ****** unfold grade_relation.
                                        right; right; right; right; right; left.
                                        split.
                                        ******* lra.
                                        ******* split; [lra|reflexivity].
                                ****** apply Forall2_cons.
                                        ******* unfold grade_relation.
                                                right; right; right; right; right; left.
                                                split.
                                                ******** lra.
                                                ******** split; [lra|reflexivity].
                                        ******* apply Forall2_cons.
                                                ******** unfold grade_relation.
                                                         right; right; right; right; right; right; left.
                                                         split.
                                                         ********* lra.
                                                         ********* split; [lra|reflexivity].
                                                ******** apply Forall2_cons.
                                                         ********* unfold grade_relation.
                                                                  right; right; right; right; right; right; left.
                                                                  split.
                                                                  ********** lra.
                                                                  ********** split; [lra|reflexivity].
                                                         ********* apply Forall2_cons.
                                                                  ********** unfold grade_relation.
                                                                              right; right; right; right; right; right; right; left.
                                                                              split.
                                                                              *********** lra.
                                                                              *********** split; [lra|reflexivity].
                                                                  ********** apply Forall2_cons.
                                                                              *********** unfold grade_relation.
                                                                                      right; right; right; right; right; right; right; left.
                                                                                      split.
                                                                                      ************ lra.
                                                                                      ************ split; [lra|reflexivity].
                                                                              *********** apply Forall2_cons.
                                                                                      ************ unfold grade_relation.
                                                                                                   right; right; right; right; right; right; right; right; left.
                                                                                                   split.
                                                                                                   ************* lra.
                                                                                                   ************* split; [lra|reflexivity].
                                                                                      ************ apply Forall2_cons.
                                                                                                   ************* unfold grade_relation.
                                                                                                                right; right; right; right; right; right; right; right; left.
                                                                                                                split.
                                                                                                                ************** lra.
                                                                                                                ************** split; [lra|reflexivity].
                                                                                                   ************* apply Forall2_cons.
                                                                                                                ************** unfold grade_relation.
                                                                                                                             right; right; right; right; right; right; right; right; right; left.
                                                                                                                             split.
                                                                                                                             *************** lra.
                                                                                                                             *************** split; [lra|reflexivity].
                                                                                                                ************** apply Forall2_cons.
                                                                                                                             *************** unfold grade_relation.
                                                                                                                                          right; right; right; right; right; right; right; right; right; left.
                                                                                                                                          split.
                                                                                                                                          **************** lra.
                                                                                                                                          **************** split; [lra|reflexivity].
                                                                                                                             *************** apply Forall2_cons.
                                                                                                                                          **************** unfold grade_relation.
                                                                                                                                                       right; right; right; right; right; right; right; right; right; right; right; left.
                                                                                                                                                       split.
                                                                                                                                                       ***************** lra.
                                                                                                                                                       ***************** split; [lra|reflexivity].
                                                                                                                                          **************** apply Forall2_cons.
                                                                                                                                                       ***************** unfold grade_relation.
                                                                                                                                                                    right; right; right; right; right; right; right; right; right; right; right; left.
                                                                                                                                                                    split.
                                                                                                                                                                    ****************** lra.
                                                                                                                                                                    ****************** split; [lra|reflexivity].
                                                                                                                                                       ***************** apply Forall2_cons.
                                                                                                                                                                    ****************** unfold grade_relation.
                                                                                                                                                                                     right; right; right; right; right; right; right; right; right; right; right; right.
                                                                                                                                                                                     split; reflexivity.
                                                                                                                                                                    ****************** apply Forall2_nil.
Qed.