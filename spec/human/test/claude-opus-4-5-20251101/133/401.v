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

Lemma is_ceil_neg_1_5 : is_ceil (-1.5) (-1)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_5_31 : is_ceil 5.310292523850798 6%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_4_63 : is_ceil (-4.6295639817413345) (-4)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_1_003 : is_ceil (-1.0030764293945094) (-1)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_4_6 : is_ceil 4.6 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_5_1 : is_ceil 5.1 6%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_1_31 : is_ceil (-1.3088872539122631) (-1)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [-1.5; 5.310292523850798; -4.6295639817413345; -1.0030764293945094; 4.6; 5.1; -1.3088872539122631; IZR 6] 152%Z.
Proof.
  unfold problem_133_spec.
  exists [(-1)%Z; 6%Z; (-4)%Z; (-1)%Z; 5%Z; 6%Z; (-1)%Z; 6%Z].
  split.
  - constructor.
    + apply is_ceil_neg_1_5.
    + constructor.
      * apply is_ceil_5_31.
      * constructor.
        -- apply is_ceil_neg_4_63.
        -- constructor.
           ++ apply is_ceil_neg_1_003.
           ++ constructor.
              ** apply is_ceil_4_6.
              ** constructor.
                 --- apply is_ceil_5_1.
                 --- constructor.
                     +++ apply is_ceil_neg_1_31.
                     +++ constructor.
                         *** apply is_ceil_IZR.
                         *** constructor.
  - simpl.
    reflexivity.
Qed.