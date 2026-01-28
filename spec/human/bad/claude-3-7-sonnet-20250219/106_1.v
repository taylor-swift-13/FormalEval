Require Import Nat.
Require Import List.
Require Import Factorial.
Require Import Lia.
Import ListNotations.

Definition problem_106_pre (n : nat) : Prop := True.

Definition problem_106_spec (n : nat) (l : list nat) : Prop :=
  let sum := fun i => Nat.div (i * (i + 1)) 2 in
  length l = n /\
  forall i, 1 <= i -> i <= n ->
    nth_error l (i - 1) = Some (if even i then fact i else sum i).

Definition example_list : list nat := [1; 2; 6; 24; 15].

Example problem_106_example :
  problem_106_spec 5 example_list.
Proof.
  unfold problem_106_spec.
  simpl.
  split.
  - reflexivity.
  - intros i Hi1 Hi2.
    (* Assert (i - 1) is a valid index *)
    assert (Hidx: i - 1 < 5).
    { lia. }
    (* We do case analysis on i *)
    destruct i.
    + lia.
    + destruct i.
      * (* i = 1 *)
        replace (1 - 1) with 0 by lia; simpl.
        unfold even.
        rewrite Nat.mod_2_1.
        simpl.
        unfold Nat.div.
        rewrite Nat.div_small; try lia.
        reflexivity.
      * destruct i.
        -- (* i = 2 *)
           replace (2 - 1) with 1 by lia; simpl.
           unfold even.
           rewrite Nat.mod_2_0.
           simpl.
           rewrite fact_2.
           reflexivity.
        -- destruct i.
           ++ (* i = 3 *)
              replace (3 - 1) with 2 by lia; simpl.
              unfold even.
              rewrite Nat.mod_2_1.
              simpl.
              unfold Nat.div.
              rewrite Nat.div_exact; try lia.
              rewrite fact_3.
              reflexivity.
           ++ destruct i.
              ** (* i = 4 *)
                 replace (4 - 1) with 3 by lia; simpl.
                 unfold even.
                 rewrite Nat.mod_2_0.
                 simpl.
                 rewrite fact_4.
                 reflexivity.
              ** destruct i.
                 --- (* i = 5 *)
                     replace (5 - 1) with 4 by lia; simpl.
                     unfold even.
                     rewrite Nat.mod_2_1.
                     simpl.
                     unfold Nat.div.
                     rewrite Nat.div_exact; try lia.
                     reflexivity.
                 --- (* i > 5 impossible *)
                     lia.
Qed.