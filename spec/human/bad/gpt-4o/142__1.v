Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Inductive sum_transformed_rel : list Z -> nat -> Z -> Prop :=
| str_nil : forall i, sum_transformed_rel [] i 0%Z
| str_cons : forall h t i s_tail term,
   (* term 是按规则对 h 应用后的值 *)
   ((Nat.eqb (i mod 3) 0 = true -> term = h * h) /\
    (Nat.eqb (i mod 3) 0 = false /\ Nat.eqb (i mod 4) 0 = true -> term = h * h * h) /\
    (Nat.eqb (i mod 3) 0 = false /\ Nat.eqb (i mod 4) 0 = false -> term = h)) ->
   sum_transformed_rel t (S i) s_tail ->
   sum_transformed_rel (h :: t) i (term + s_tail).

Definition problem_142_pre (lst : list Z) : Prop := True.

Definition problem_142_spec (lst : list Z) (res : Z) : Prop :=
  sum_transformed_rel lst 0%nat res.

Example test_case_1 :
  problem_142_spec [1%Z; 2%Z; 3%Z] 6%Z.
Proof.
  unfold problem_142_spec.
  apply str_cons with (term := 1).
  - split; [intros H; discriminate | split; intros [_ H]; discriminate].
  - apply str_cons with (term := 2).
    + split; [intros H; discriminate | split; intros [_ H]; discriminate].
    + apply str_cons with (term := 3 * 3).
      * split; [intros _; reflexivity | split; intros [_ H]; discriminate].
      * apply str_nil.
Qed.