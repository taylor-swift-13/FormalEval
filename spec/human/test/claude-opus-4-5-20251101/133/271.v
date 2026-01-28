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

Lemma is_ceil_intro : forall x z, (IZR z - 1 < x) -> (x <= IZR z) -> is_ceil x z.
Proof.
  intros x z H1 H2.
  unfold is_ceil.
  split; assumption.
Qed.

Example test_problem_133 :
  problem_133_spec [0.1; 1.840256743666684; 1.1; 3.2; 4.234081562814888; 6.851261387881998; 6.7; 3.2] 164%Z.
Proof.
  unfold problem_133_spec.
  exists [1%Z; 2%Z; 2%Z; 4%Z; 5%Z; 7%Z; 7%Z; 4%Z].
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
  - simpl.
    reflexivity.
Qed.