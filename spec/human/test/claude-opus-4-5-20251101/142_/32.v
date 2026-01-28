Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Inductive sum_transformed_rel : list Z -> nat -> Z -> Prop :=
| str_nil : forall i, sum_transformed_rel [] i 0%Z
| str_cons : forall h t i s_tail term,
   ((Nat.eqb (i mod 3) 0 = true -> term = h * h) /\
    (Nat.eqb (i mod 3) 0 = false /\ Nat.eqb (i mod 4) 0 = true -> term = h * h * h) /\
    (Nat.eqb (i mod 3) 0 = false /\ Nat.eqb (i mod 4) 0 = false -> term = h)) ->
   sum_transformed_rel t (S i) s_tail ->
   sum_transformed_rel (h :: t) i (term + s_tail).

Definition problem_142_pre (lst : list Z) : Prop := True.

Definition problem_142_spec (lst : list Z) (res : Z) : Prop :=
  sum_transformed_rel lst 0%nat res.

Example test_142 : problem_142_spec [6%Z; 18%Z; 12%Z; 15%Z; 18%Z; 21%Z; 24%Z; 27%Z; 30%Z] 33747%Z.
Proof.
  unfold problem_142_spec.
  apply (str_cons 6 [18%Z; 12%Z; 15%Z; 18%Z; 21%Z; 24%Z; 27%Z; 30%Z] 0 33711 36).
  - split; [| split].
    + intros _. reflexivity.
    + intros [H1 H2]. simpl in H1. discriminate.
    + intros [H1 H2]. simpl in H1. discriminate.
  - apply (str_cons 18 [12%Z; 15%Z; 18%Z; 21%Z; 24%Z; 27%Z; 30%Z] 1 33693 18).
    + split; [| split].
      * intros H. simpl in H. discriminate.
      * intros [H1 H2]. simpl in H2. discriminate.
      * intros [H1 H2]. reflexivity.
    + apply (str_cons 12 [15%Z; 18%Z; 21%Z; 24%Z; 27%Z; 30%Z] 2 33681 12).
      * split; [| split].
        -- intros H. simpl in H. discriminate.
        -- intros [H1 H2]. simpl in H2. discriminate.
        -- intros [H1 H2]. reflexivity.
      * apply (str_cons 15 [18%Z; 21%Z; 24%Z; 27%Z; 30%Z] 3 33456 225).
        -- split; [| split].
           ++ intros _. reflexivity.
           ++ intros [H1 H2]. simpl in H1. discriminate.
           ++ intros [H1 H2]. simpl in H1. discriminate.
        -- apply (str_cons 18 [21%Z; 24%Z; 27%Z; 30%Z] 4 27624 5832).
           ++ split; [| split].
              ** intros H. simpl in H. discriminate.
              ** intros [H1 H2]. reflexivity.
              ** intros [H1 H2]. simpl in H2. discriminate.
           ++ apply (str_cons 21 [24%Z; 27%Z; 30%Z] 5 27603 21).
              ** split; [| split].
                 --- intros H. simpl in H. discriminate.
                 --- intros [H1 H2]. simpl in H2. discriminate.
                 --- intros [H1 H2]. reflexivity.
              ** apply (str_cons 24 [27%Z; 30%Z] 6 27027 576).
                 --- split; [| split].
                     +++ intros _. reflexivity.
                     +++ intros [H1 H2]. simpl in H1. discriminate.
                     +++ intros [H1 H2]. simpl in H1. discriminate.
                 --- apply (str_cons 27 [30%Z] 7 27000 27).
                     +++ split; [| split].
                         *** intros H. simpl in H. discriminate.
                         *** intros [H1 H2]. simpl in H2. discriminate.
                         *** intros [H1 H2]. reflexivity.
                     +++ apply (str_cons 30 [] 8 0 27000).
                         *** split; [| split].
                             ---- intros H. simpl in H. discriminate.
                             ---- intros [H1 H2]. reflexivity.
                             ---- intros [H1 H2]. simpl in H2. discriminate.
                         *** apply str_nil.
Qed.