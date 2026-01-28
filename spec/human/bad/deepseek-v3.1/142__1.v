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

Definition problem_142_spec (lst : list Z) (res : Z) : Prop :=
  sum_transformed_rel lst 0%nat res.

Example test_case_1 : problem_142_spec [1%Z; 2%Z; 3%Z] 6%Z.
Proof.
  unfold problem_142_spec.
  apply str_cons with (term := 1%Z).
  - split.
    + intro H. 
      compute in H. discriminate H.
    + split.
      * intros [H1 H2]. 
        compute in H1, H2. discriminate H2.
      * intro H. reflexivity.
  - apply str_cons with (term := 2%Z).
    + split.
      * intro H.
        compute in H. discriminate H.
      * split.
        -- intros [H1 H2].
           compute in H1, H2. discriminate H2.
        -- intro H. reflexivity.
    + apply str_cons with (term := 9%Z).
      * split.
        -- intro H. reflexivity.
        -- split.
           ++ intros [H1 H2].
              compute in H1. discriminate H1.
           ++ intro H. reflexivity.
      * apply str_nil.
    + compute. reflexivity.
  + compute. reflexivity.
Qed.