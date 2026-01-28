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

Lemma is_ceil_neg3 : is_ceil (-3.2596671445918055) (-3)%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Lemma is_ceil_0_1 : is_ceil 0.1 1%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Lemma is_ceil_1_5 : is_ceil 1.5 2%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Lemma is_ceil_2_9 : is_ceil 2.9 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Lemma is_ceil_2_228 : is_ceil 2.228516548185696 3%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Lemma is_ceil_4_234 : is_ceil 4.234081562814888 5%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Lemma is_ceil_6_7 : is_ceil 6.7 7%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Lemma is_ceil_7_414 : is_ceil 7.4145549533273405 8%Z.
Proof.
  unfold is_ceil.
  simpl.
  split; lra.
Qed.

Example test_problem_133 :
  problem_133_spec [-3.2596671445918055; 0.1; 1.5; 2.9; 2.228516548185696; 4.234081562814888; 6.7; 7.4145549533273405; 6.7; 2.9; 7.4145549533273405] 292%Z.
Proof.
  unfold problem_133_spec.
  exists [(-3)%Z; 1%Z; 2%Z; 3%Z; 3%Z; 5%Z; 7%Z; 8%Z; 7%Z; 3%Z; 8%Z].
  split.
  - constructor.
    + apply is_ceil_neg3.
    + constructor.
      * apply is_ceil_0_1.
      * constructor.
        -- apply is_ceil_1_5.
        -- constructor.
           ++ apply is_ceil_2_9.
           ++ constructor.
              ** apply is_ceil_2_228.
              ** constructor.
                 --- apply is_ceil_4_234.
                 --- constructor.
                     +++ apply is_ceil_6_7.
                     +++ constructor.
                         *** apply is_ceil_7_414.
                         *** constructor.
                             ---- apply is_ceil_6_7.
                             ---- constructor.
                                  ++++ apply is_ceil_2_9.
                                  ++++ constructor.
                                       **** apply is_ceil_7_414.
                                       **** constructor.
  - simpl.
    reflexivity.
Qed.