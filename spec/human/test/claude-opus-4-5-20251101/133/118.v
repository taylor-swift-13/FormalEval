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

Lemma is_ceil_314_4 : is_ceil 3.14 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg809_neg8 : is_ceil (-8.09) (-8)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_271_3 : is_ceil 2.71 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_069_1 : is_ceil 0.69 1%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_162_2 : is_ceil 1.62 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg999_neg9 : is_ceil (-9.99) (-9)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_628_7 : is_ceil 6.28 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg1404_neg14 : is_ceil (-14.04) (-14)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [3.14; -8.09; 2.71; 0.69; 1.62; -9.99; 6.28; -14.04] 420%Z.
Proof.
  unfold problem_133_spec.
  exists [4%Z; (-8)%Z; 3%Z; 1%Z; 2%Z; (-9)%Z; 7%Z; (-14)%Z].
  split.
  - constructor.
    + apply is_ceil_314_4.
    + constructor.
      * apply is_ceil_neg809_neg8.
      * constructor.
        -- apply is_ceil_271_3.
        -- constructor.
           ++ apply is_ceil_069_1.
           ++ constructor.
              ** apply is_ceil_162_2.
              ** constructor.
                 --- apply is_ceil_neg999_neg9.
                 --- constructor.
                     +++ apply is_ceil_628_7.
                     +++ constructor.
                         *** apply is_ceil_neg1404_neg14.
                         *** constructor.
  - simpl.
    reflexivity.
Qed.