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

Lemma is_ceil_intro : forall x : R, forall z : Z,
  (IZR z - 1 < x) -> (x <= IZR z) -> is_ceil x z.
Proof.
  intros x z H1 H2.
  unfold is_ceil.
  split; assumption.
Qed.

Example test_problem_133 :
  problem_133_spec [4.234081562814888; 0.1; 4.715583291999385; -3.7; 3.2; -3.3629337697813977; 4.6; 5.1; 6.7; 6.7] 244%Z.
Proof.
  unfold problem_133_spec.
  exists [5%Z; 1%Z; 5%Z; (-3)%Z; 4%Z; (-3)%Z; 5%Z; 6%Z; 7%Z; 7%Z].
  split.
  - constructor.
    + apply is_ceil_intro; simpl; lra.
    + constructor.
      * apply is_ceil_intro; simpl; lra.
      * constructor.
        -- apply is_ceil_intro; simpl; lra.
        -- constructor.
           ++ apply is_ceil_intro; simpl; lra.
           ++ constructor.
              ** apply is_ceil_intro; simpl; lra.
              ** constructor.
                 --- apply is_ceil_intro; simpl; lra.
                 --- constructor.
                     +++ apply is_ceil_intro; simpl; lra.
                     +++ constructor.
                         *** apply is_ceil_intro; simpl; lra.
                         *** constructor.
                             ---- apply is_ceil_intro; simpl; lra.
                             ---- constructor.
                                  ++++ apply is_ceil_intro; simpl; lra.
                                  ++++ constructor.
  - simpl.
    reflexivity.
Qed.