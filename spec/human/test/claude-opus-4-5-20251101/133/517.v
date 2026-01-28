Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition is_ceil (x : R) (z : Z) : Prop :=
  (IZR z - 1 < x) /\ (x <= IZR z).

Definition problem_133_pre (lst : list R) : Prop := True.

Definition problem_133_spec (lst : list R) (s : Z) : Prop :=
  exists zs : list Z,
    Forall2 is_ceil lst zs /\
    s = fold_right Z.add 0%Z (map (fun z => Z.mul z z) zs).

Lemma is_ceil_IZR : forall z : Z, is_ceil (IZR z) z.
Proof.
  intro z.
  unfold is_ceil.
  split.
  - lra.
  - lra.
Qed.

Lemma is_ceil_2_5 : is_ceil (5/2) 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_3_7 : is_ceil (-37/10) (-3)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_4_716809497407311 : is_ceil (-4716809497407311/1000000000000000) (-4)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_6_5 : is_ceil (-13/2) (-6)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_1_1 : is_ceil (11/10) 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [5/2; -37/10; -4716809497407311/1000000000000000; -13/2; IZR 6; IZR 7; 11/10; 5/2; 5/2] 177%Z.
Proof.
  unfold problem_133_spec.
  exists [3%Z; (-3)%Z; (-4)%Z; (-6)%Z; 6%Z; 7%Z; 2%Z; 3%Z; 3%Z].
  split.
  - constructor.
    + apply is_ceil_2_5.
    + constructor.
      * apply is_ceil_neg_3_7.
      * constructor.
        -- apply is_ceil_neg_4_716809497407311.
        -- constructor.
           ++ apply is_ceil_neg_6_5.
           ++ constructor.
              ** apply is_ceil_IZR.
              ** constructor.
                 --- apply is_ceil_IZR.
                 --- constructor.
                     +++ apply is_ceil_1_1.
                     +++ constructor.
                         *** apply is_ceil_2_5.
                         *** constructor.
                             ---- apply is_ceil_2_5.
                             ---- constructor.
  - simpl.
    reflexivity.
Qed.