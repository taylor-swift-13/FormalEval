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

Lemma is_ceil_01_1 : is_ceil 0.1 1%Z.
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

Lemma is_ceil_neg4716_neg4 : is_ceil (-4.716809497407311) (-4)%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_29_3 : is_ceil 2.9 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_4129_5 : is_ceil 4.129563514953585 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_4967_5 : is_ceil 4.967726321372912 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_3499_4 : is_ceil 3.499530218204873 4%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_51_6 : is_ceil 5.1 6%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_67_7 : is_ceil 6.7 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_4164_5 : is_ceil 4.164996313633066 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Lemma is_ceil_46_5 : is_ceil 4.6 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  lra.
Qed.

Example test_problem_133 :
  problem_133_spec [0.1; 0.1; -8.09; -4.716809497407311; 2.9; 4.129563514953585; 4.967726321372912; 3.499530218204873; 5.1; 6.7; 4.164996313633066; 4.6] 292%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; 1%Z; (-8)%Z; (-4)%Z; 3%Z; 5%Z; 5%Z; 4%Z; 6%Z; 7%Z; 5%Z; 5%Z].
  split.
  - constructor.
    + apply is_ceil_01_1.
    + constructor.
      * apply is_ceil_01_1.
      * constructor.
        -- apply is_ceil_neg809_neg8.
        -- constructor.
           ++ apply is_ceil_neg4716_neg4.
           ++ constructor.
              ** apply is_ceil_29_3.
              ** constructor.
                 --- apply is_ceil_4129_5.
                 --- constructor.
                     +++ apply is_ceil_4967_5.
                     +++ constructor.
                         *** apply is_ceil_3499_4.
                         *** constructor.
                             ---- apply is_ceil_51_6.
                             ---- constructor.
                                  ++++ apply is_ceil_67_7.
                                  ++++ constructor.
                                       **** apply is_ceil_4164_5.
                                       **** constructor.
                                            ----- apply is_ceil_46_5.
                                            ----- constructor.
  - simpl.
    reflexivity.
Qed.