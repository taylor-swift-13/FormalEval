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

Lemma is_ceil_1 : is_ceil 0.1 1%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_2 : is_ceil 1.5 2%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_3 : is_ceil 2.9 3%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_5 : is_ceil 4.234081562814888 5%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_7a : is_ceil 6.851261387881998 7%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_7b : is_ceil 6.7 7%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_1b : is_ceil 0.12719557110029214 1%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Lemma is_ceil_4 : is_ceil 3.263069699177953 4%Z.
Proof.
  unfold is_ceil. simpl. lra.
Qed.

Example test_problem_133 :
  problem_133_spec [0.1; 1.5; 2.9; 4.234081562814888; 6.851261387881998; 6.7; 0.12719557110029214; 3.263069699177953; 6.851261387881998] 203%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; 2%Z; 3%Z; 5%Z; 7%Z; 7%Z; 1%Z; 4%Z; 7%Z].
  split.
  - constructor.
    + apply is_ceil_1.
    + constructor.
      * apply is_ceil_2.
      * constructor.
        -- apply is_ceil_3.
        -- constructor.
           ++ apply is_ceil_5.
           ++ constructor.
              ** apply is_ceil_7a.
              ** constructor.
                 --- apply is_ceil_7b.
                 --- constructor.
                     +++ apply is_ceil_1b.
                     +++ constructor.
                         *** apply is_ceil_4.
                         *** constructor.
                             ---- apply is_ceil_7a.
                             ---- constructor.
  - simpl.
    reflexivity.
Qed.