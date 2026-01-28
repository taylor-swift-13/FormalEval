Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Program.Basics.
Require Import Coq.micromega.Lia.

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

Definition problem_81_spec (gpas : list R) (grades : list string) : Prop :=
  Forall2 grade_relation gpas grades.

Lemma test_case_81 : problem_81_spec [4.0; 3; 1.7; 2; 3.5] ["A+"; "B"; "C-"; "C"; "A-"].
Proof.
  unfold problem_81_spec.
  constructor.
  - unfold grade_relation. left. split.
    + reflexivity.
    + reflexivity.
  - constructor.
    + unfold grade_relation. right. right. right. left. repeat split.
      * apply Rlt_gt. apply Rlt_trans with (r2 := 3.3).
        -- apply Rlt_trans with (r2 := 2.7).
           ++ apply Rlt_trans with (r2 := 2.3).
              ** apply Rlt_trans with (r2 := 2.0).
                 --- apply Rlt_trans with (r2 := 1.7).
                     +++ apply Rlt_trans with (r2 := 1.3).
                         *** apply Rlt_trans with (r2 := 1.0).
                             ---- apply Rlt_trans with (r2 := 0.7).
                                  ----- apply Rlt_trans with (r2 := 0.0).
                                        +++++ apply Rlt_0_1.
                                        +++++ discriminate.
                                  ----- apply IZR_lt. lia.
                             ---- apply IZR_lt. lia.
                         *** apply Rlt_gt. lra.
                     +++ apply Rlt_gt. lra.
                 --- apply Rlt_gt. lra.
              ** apply Rlt_gt. lra.
           ++ apply Rlt_gt. lra.
        -- apply Rlt_gt. lra.
      * apply Rle_refl.
      * reflexivity.
    + constructor.
      * unfold grade_relation. right. right. right. right. right. right. right. left. repeat split.
        -- apply Rlt_gt. apply Rlt_trans with (r2 := 1.3).
           ++ apply Rlt_trans with (r2 := 1.0).
              ** apply Rlt_trans with (r2 := 0.7).
                 --- apply Rlt_trans with (r2 := 0.0).
                     +++ apply Rlt_0_1.
                     +++ discriminate.
                 --- apply IZR_lt. lia.
              ** apply IZR_lt. lia.
           ++ apply Rlt_gt. lra.
        -- apply Rle_refl.
        -- reflexivity.
      * constructor.
        -- unfold grade_relation. right. right. right. right. right. right. left. repeat split.
           ++ apply Rlt_gt. apply Rlt_trans with (r2 := 1.7).
              ** apply Rlt_trans with (r2 := 1.3).
                 --- apply Rlt_trans with (r2 := 1.0).
                     +++ apply Rlt_trans with (r2 := 0.7).
                         *** apply Rlt_trans with (r2 := 0.0).
                             ---- apply Rlt_0_1.
                             ---- discriminate.
                         *** apply IZR_lt. lia.
                     +++ apply IZR_lt. lia.
                 --- apply Rlt_gt. lra.
              ** apply Rlt_gt. lra.
           ++ apply Rle_refl.
           ++ reflexivity.
        -- constructor.
           ++ unfold grade_relation. right. right. right. left. repeat split.
              ** apply Rlt_gt. apply Rlt_trans with (r2 := 3.0).
                 --- apply Rlt_trans with (r2 := 2.7).
                     +++ apply Rlt_trans with (r2 := 2.3).
                         *** apply Rlt_trans with (r2 := 2.0).
                             ---- apply Rlt_trans with (r2 := 1.7).
                                 ++++ apply Rlt_trans with (r2 := 1.3).
                                      **** apply Rlt_trans with (r2 := 1.0).
                                           +++++ apply Rlt_trans with (r2 := 0.7).
                                                 ------ apply Rlt_trans with (r2 := 0.0).
                                                        ++++++ apply Rlt_0_1.
                                                        ++++++ discriminate.
                                                 ------ apply IZR_lt. lia.
                                           +++++ apply IZR_lt. lia.
                                      **** apply Rlt_gt. lra.
                                 ++++ apply Rlt_gt. lra.
                             ---- apply Rlt_gt. lra.
                         *** apply Rlt_gt. lra.
                     +++ apply Rlt_gt. lra.
                 --- apply Rlt_gt. lra.
              ** apply Rle_refl.
              ** reflexivity.
           ++ constructor.
Qed.