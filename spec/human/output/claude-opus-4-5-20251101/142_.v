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

Example test_142 : problem_142_spec [1%Z; 2%Z; 3%Z] 6%Z.
Proof.
  unfold problem_142_spec.
  (* Index 0: 0 mod 3 = 0, so square: 1*1 = 1 *)
  (* Index 1: 1 mod 3 = 1 ≠ 0, 1 mod 4 = 1 ≠ 0, so keep: 2 *)
  (* Index 2: 2 mod 3 = 2 ≠ 0, 2 mod 4 = 2 ≠ 0, so keep: 3 *)
  (* Sum = 1 + 2 + 3 = 6 *)
  
  (* For element 1 at index 0 *)
  apply (str_cons 1 [2%Z; 3%Z] 0 5 1).
  - split; [| split].
    + intros _. reflexivity.
    + intros [H1 H2]. simpl in H1. discriminate.
    + intros [H1 H2]. simpl in H1. discriminate.
  
  (* For element 2 at index 1 *)
  - apply (str_cons 2 [3%Z] 1 3 2).
    + split; [| split].
      * intros H. simpl in H. discriminate.
      * intros [H1 H2]. simpl in H2. discriminate.
      * intros [H1 H2]. reflexivity.
    
    (* For element 3 at index 2 *)
    + apply (str_cons 3 [] 2 0 3).
      * split; [| split].
        -- intros H. simpl in H. discriminate.
        -- intros [H1 H2]. simpl in H2. discriminate.
        -- intros [H1 H2]. reflexivity.
      * apply str_nil.
Qed.