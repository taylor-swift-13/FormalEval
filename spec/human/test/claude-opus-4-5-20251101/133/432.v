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
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_2_71 : is_ceil 2.71 3%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_2_49 : is_ceil 2.4936669865395658 3%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_4_23 : is_ceil 4.234081562814888 5%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_6_85 : is_ceil 6.851261387881998 7%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_8_52 : is_ceil 8.527593815012729 9%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_6_7 : is_ceil 6.7 7%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_0_58 : is_ceil 0.584204380758542 1%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Example test_problem_133 :
  problem_133_spec [1.5; 2.71; 2.4936669865395658; 4.234081562814888; 6.851261387881998; 8.527593815012729; 6.7; 4.234081562814888; 1.5; 2.4936669865395658; 0.584204380758542; 6.7] 314%Z.
Proof.
  unfold problem_133_spec.
  exists [2%Z; 3%Z; 3%Z; 5%Z; 7%Z; 9%Z; 7%Z; 5%Z; 2%Z; 3%Z; 1%Z; 7%Z].
  split.
  - constructor.
    + apply is_ceil_1_5.
    + constructor.
      * apply is_ceil_2_71.
      * constructor.
        -- apply is_ceil_2_49.
        -- constructor.
           ++ apply is_ceil_4_23.
           ++ constructor.
              ** apply is_ceil_6_85.
              ** constructor.
                 --- apply is_ceil_8_52.
                 --- constructor.
                     +++ apply is_ceil_6_7.
                     +++ constructor.
                         *** apply is_ceil_4_23.
                         *** constructor.
                             ---- apply is_ceil_1_5.
                             ---- constructor.
                                  ++++ apply is_ceil_2_49.
                                  ++++ constructor.
                                       **** apply is_ceil_0_58.
                                       **** constructor.
                                            ----- apply is_ceil_6_7.
                                            ----- constructor.
  - simpl. reflexivity.
Qed.