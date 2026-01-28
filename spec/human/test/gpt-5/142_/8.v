Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Arith.Arith Lia.
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

Example test_case_sum_squares :
  problem_142_spec [-56%Z; -99%Z; 1%Z; 0%Z; -2%Z] 3030%Z.
Proof.
  unfold problem_142_spec.
  replace 3030%Z with (3136%Z + (-106%Z)) by lia.
  apply (str_cons (-56%Z) [-99%Z; 1%Z; 0%Z; -2%Z] 0%nat (-106%Z) 3136%Z).
  split; [ intros _; reflexivity
        | split; [ intros [H3 H4]; simpl in H3; discriminate
                  | intros [H3 H4]; simpl in H3; discriminate ] ].
  apply (str_cons (-99%Z) [1%Z; 0%Z; -2%Z] 1%nat (-7%Z) (-99%Z)).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 1%Z [0%Z; -2%Z] 2%nat (-8%Z) 1%Z).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; simpl in H2; discriminate
                  | intros [H1 H2]; reflexivity ] ].
  apply (str_cons 0%Z [-2%Z] 3%nat (-8%Z) 0%Z).
  split; [ intros _; reflexivity
        | split; [ intros [H1 H2]; simpl in H1; discriminate
                  | intros [H1 H2]; simpl in H1; discriminate ] ].
  apply (str_cons (-2%Z) [] 4%nat 0%Z (-8%Z)).
  split; [ intros H; simpl in H; discriminate
        | split; [ intros [H1 H2]; reflexivity
                  | intros [H1 H2]; simpl in H2; discriminate ] ].
  apply (str_nil 5%nat).
Qed.