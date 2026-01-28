Require Import List.
Require Import ZArith.
Require Import Arith.
Require Import Nat.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition problem_5_pre (input output : list Z) : Prop := True.

Definition problem_5_spec (input output : list Z) (d : Z) : Prop :=
  (input = [] -> output = []) /\
  (forall n : nat,
      length input = n -> 1 <= n ->
      length output = 2 * n - 1 /\
      forall i : nat, i < 2 * n - 1 ->
        (Nat.Even i -> nth_error output i = nth_error input (i / 2)) /\
        (Nat.Odd i -> nth_error output i = Some d)
  ).

Example test_intersperse_custom : 
  problem_5_spec [[5%Z; 10%Z; 15%Z]; 0%Z] [5%Z; 0%Z; 10%Z; 0%Z; 15%Z] 0%Z.
Proof.
  unfold problem_5_spec.
  split.
  - intro H. reflexivity.
  - intros n Hlen Hn.
    simpl in Hlen.
    assert (n = 2) by lia.
    subst n.
    split.
    + rewrite Hlen.
      reflexivity.
    + intros i Hi.
      simpl.
      rewrite Hlen in Hi.
      assert (i < 2 * 2 - 1) by lia.
      destruct (lt_eq_lt_dec i (2)) as [[Hi1 | Hi2] | Hi3].
      * (* i < 2 *)
        simpl.
        rewrite Nat.div2_small; [| lia].
        rewrite nth_error_app2.
        -- reflexivity.
        -- lia.
      * (* i = 2 *)
        subst i.
        simpl.
        rewrite nth_error_app1.
        -- rewrite Nat.div2_self; lia.
        -- lia.
      * (* i > 2 *)
        simpl.
        rewrite nth_error_app2.
        -- lia.
        -- lia.
Qed.