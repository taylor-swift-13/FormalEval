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

Lemma is_ceil_8_634 : is_ceil 8.634480834505068 9%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_3_4 : is_ceil (-3.4) (-3)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_3_2512 : is_ceil (-3.2512040012099304) (-3)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_3_2596 : is_ceil (-3.2596671445918055) (-3)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [8.634480834505068; IZR 1; IZR (-5); IZR 2; -3.4; -3.2512040012099304; -3.2596671445918055; IZR (-6); -3.2512040012099304] 183%Z.
Proof.
  unfold problem_133_spec.
  exists [9%Z; 1%Z; (-5)%Z; 2%Z; (-3)%Z; (-3)%Z; (-3)%Z; (-6)%Z; (-3)%Z].
  split.
  - constructor.
    + apply is_ceil_8_634.
    + constructor.
      * apply is_ceil_IZR.
      * constructor.
        -- apply is_ceil_IZR.
        -- constructor.
           ++ apply is_ceil_IZR.
           ++ constructor.
              ** apply is_ceil_neg_3_4.
              ** constructor.
                 --- apply is_ceil_neg_3_2512.
                 --- constructor.
                     +++ apply is_ceil_neg_3_2596.
                     +++ constructor.
                         *** apply is_ceil_IZR.
                         *** constructor.
                             ---- apply is_ceil_neg_3_2512.
                             ---- constructor.
  - simpl.
    reflexivity.
Qed.