Require Import Coq.Reals.Reals.
Require Import Coq.Reals.R_sqrt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition triangle_area_spec (a b c area : R) : Prop :=
((a + b <= c \/ a + c <= b \/ b + c <= a) /\ area = -1) \/
(~(a + b <= c \/ a + c <= b \/ b + c <= a) /\
 let p := (a + b + c) / 2 in
 let x := sqrt (p * (p - a) * (p - b) * (p - c)) in
 exists k : Z,
   area = IZR k / 100 /\
   forall n : Z,
     Rabs (x * 100 - IZR k) <= Rabs (x * 100 - IZR n) /\
     (n <> k -> Rabs (x * 100 - IZR k) = Rabs (x * 100 - IZR n) -> Zeven k)).

Lemma sqrt_36_eq_6 : sqrt 36 = 6.
Proof.
  rewrite <- (sqrt_square 6).
  - f_equal. ring.
  - lra.
Qed.

Example triangle_area_example : triangle_area_spec 3 4 5 6.
Proof.
  unfold triangle_area_spec.
  right.
  split.
  - intros [H | [H | H]]; lra.
  - simpl.
    exists 600%Z.
    split.
    + field.
    + intros n.
      assert (Hp_eq: (3 + 4 + 5) / 2 = 6) by field.
      assert (Hprod: 6 * (6 - 3) * (6 - 4) * (6 - 5) = 36) by ring.
      assert (Hsqrt_val: sqrt (6 * (6 - 3) * (6 - 4) * (6 - 5)) = 6).
      {
        rewrite Hprod.
        exact sqrt_36_eq_6.
      }
      split.
      * assert (Hgoal: sqrt ((3 + 4 + 5) / 2 * ((3 + 4 + 5) / 2 - 3) * ((3 + 4 + 5) / 2 - 4) * ((3 + 4 + 5) / 2 - 5)) = 6).
        {
          replace ((3 + 4 + 5) / 2) with 6 by field.
          replace (6 - 3) with 3 by ring.
          replace (6 - 4) with 2 by ring.
          replace (6 - 5) with 1 by ring.
          replace (6 * 3 * 2 * 1) with 36 by ring.
          exact sqrt_36_eq_6.
        }
        rewrite Hgoal.
        replace (6 * 100 - IZR 600) with 0.
        -- rewrite Rabs_R0. apply Rabs_pos.
        -- simpl. ring.
      * intros Hneq Habs_eq.
        simpl. auto.
Qed.