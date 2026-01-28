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

Lemma is_ceil_3_4 : is_ceil (17/5) 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_3_4 : is_ceil (-(17/5)) (-3)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_4_6 : is_ceil (-(23/5)) (-4)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg_5_1 : is_ceil (-(51/10)) (-5)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [IZR 2; 17/5; -(17/5); IZR (-5); -(23/5); IZR (-6); IZR 3; -(51/10); IZR (-6); -(23/5); -(23/5)] 208%Z.
Proof.
  unfold problem_133_spec.
  exists [2%Z; 4%Z; (-3)%Z; (-5)%Z; (-4)%Z; (-6)%Z; 3%Z; (-5)%Z; (-6)%Z; (-4)%Z; (-4)%Z].
  split.
  - constructor.
    + apply is_ceil_IZR.
    + constructor.
      * apply is_ceil_3_4.
      * constructor.
        -- apply is_ceil_neg_3_4.
        -- constructor.
           ++ apply is_ceil_IZR.
           ++ constructor.
              ** apply is_ceil_neg_4_6.
              ** constructor.
                 --- apply is_ceil_IZR.
                 --- constructor.
                     +++ apply is_ceil_IZR.
                     +++ constructor.
                         *** apply is_ceil_neg_5_1.
                         *** constructor.
                             ---- apply is_ceil_IZR.
                             ---- constructor.
                                  ++++ apply is_ceil_neg_4_6.
                                  ++++ constructor.
                                       **** apply is_ceil_neg_4_6.
                                       **** constructor.
  - simpl.
    reflexivity.
Qed.