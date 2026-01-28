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

Lemma is_ceil_neg1 : is_ceil (-1) (-1)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg4_33 : is_ceil (-4.33753565336939) (-4)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_4 : is_ceil (3.4) 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg8_09 : is_ceil (-8.09) (-8)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg4_6 : is_ceil (-4.6) (-4)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_5_1 : is_ceil (5.1) 6%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [IZR 1; IZR (-1); IZR 3; -4.33753565336939; 3.4; -8.09; -4.6; 5.1; IZR 6; IZR 6; 5.1] 267%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; (-1)%Z; 3%Z; (-4)%Z; 4%Z; (-8)%Z; (-4)%Z; 6%Z; 6%Z; 6%Z; 6%Z].
  split.
  - constructor.
    + apply is_ceil_IZR.
    + constructor.
      * apply is_ceil_IZR.
      * constructor.
        -- apply is_ceil_IZR.
        -- constructor.
           ++ apply is_ceil_neg4_33.
           ++ constructor.
              ** apply is_ceil_3_4.
              ** constructor.
                 --- apply is_ceil_neg8_09.
                 --- constructor.
                     +++ apply is_ceil_neg4_6.
                     +++ constructor.
                         *** apply is_ceil_5_1.
                         *** constructor.
                             ---- apply is_ceil_IZR.
                             ---- constructor.
                                  ++++ apply is_ceil_IZR.
                                  ++++ constructor.
                                       **** apply is_ceil_5_1.
                                       **** constructor.
  - simpl.
    reflexivity.
Qed.