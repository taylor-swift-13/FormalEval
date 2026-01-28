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

Lemma is_ceil_5_4p5 : is_ceil 4.5 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_1_0p1 : is_ceil 0.1 1%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_2_1p5 : is_ceil 1.5 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3_2p0026 : is_ceil 2.0026403456856325 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_4_3p2 : is_ceil 3.2 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_7_6p85 : is_ceil 6.851261387881998 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_neg6_neg6p77 : is_ceil (-6.773948579844583) (-6)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_7_6p7 : is_ceil 6.7 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_5_4p23 : is_ceil 4.234081562814888 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [4.5; 0.1; 1.5; 2.0026403456856325; 3.2; 6.851261387881998; -6.773948579844583; 6.7; 4.234081562814888; 4.5] 239%Z.
Proof.
  unfold problem_133_spec.
  exists [5%Z; 1%Z; 2%Z; 3%Z; 4%Z; 7%Z; (-6)%Z; 7%Z; 5%Z; 5%Z].
  split.
  - constructor.
    + apply is_ceil_5_4p5.
    + constructor.
      * apply is_ceil_1_0p1.
      * constructor.
        -- apply is_ceil_2_1p5.
        -- constructor.
           ++ apply is_ceil_3_2p0026.
           ++ constructor.
              ** apply is_ceil_4_3p2.
              ** constructor.
                 --- apply is_ceil_7_6p85.
                 --- constructor.
                     +++ apply is_ceil_neg6_neg6p77.
                     +++ constructor.
                         *** apply is_ceil_7_6p7.
                         *** constructor.
                             ---- apply is_ceil_5_4p23.
                             ---- constructor.
                                  ++++ apply is_ceil_5_4p5.
                                  ++++ constructor.
  - simpl.
    reflexivity.
Qed.