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

Lemma is_ceil_1_5 : is_ceil 1.5 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_1_1 : is_ceil 1.1 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_2 : is_ceil 3.2 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_6_7 : is_ceil 6.7 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_0_061 : is_ceil 0.061283494508126014 1%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_0_621 : is_ceil 0.6212597321029525 1%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_6_851 : is_ceil 6.851261387881998 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_8_634 : is_ceil 8.634480834505068 9%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_4_234 : is_ceil 4.234081562814888 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [0.061283494508126014; 1.5; 1.1; 3.2; 0.6212597321029525; 6.851261387881998; 8.634480834505068; 6.7; 4.234081562814888; 6.7] 279%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; 2%Z; 2%Z; 4%Z; 1%Z; 7%Z; 9%Z; 7%Z; 5%Z; 7%Z].
  split.
  - constructor.
    + apply is_ceil_0_061.
    + constructor.
      * apply is_ceil_1_5.
      * constructor.
        -- apply is_ceil_1_1.
        -- constructor.
           ++ apply is_ceil_3_2.
           ++ constructor.
              ** apply is_ceil_0_621.
              ** constructor.
                 --- apply is_ceil_6_851.
                 --- constructor.
                     +++ apply is_ceil_8_634.
                     +++ constructor.
                         *** apply is_ceil_6_7.
                         *** constructor.
                             ---- apply is_ceil_4_234.
                             ---- constructor.
                                  ++++ apply is_ceil_6_7.
                                  ++++ constructor.
  - simpl.
    reflexivity.
Qed.