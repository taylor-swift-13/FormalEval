Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.

Inductive sum_odd_in_even_pos_rel : list nat -> nat -> nat -> Prop :=
| soep_nil : forall i, sum_odd_in_even_pos_rel nil i 0%nat
| soep_match : forall h t i s_tail, Nat.even i = true -> Nat.even h = false ->
    sum_odd_in_even_pos_rel t (S i) s_tail ->
    sum_odd_in_even_pos_rel (h :: t) i (h + s_tail)
| soep_skip : forall h t i s_tail, (Nat.even i = false \/ Nat.even h = true) ->
    sum_odd_in_even_pos_rel t (S i) s_tail ->
    sum_odd_in_even_pos_rel (h :: t) i s_tail.

Definition problem_121_pre (l : list nat) : Prop := l <> [].

Definition problem_121_spec (l : list nat) (output : nat) : Prop :=
  sum_odd_in_even_pos_rel l 0%nat output.

Example problem_121_test_case :
  problem_121_spec [0%nat; 1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat; 7%nat; 6%nat] 0%nat.
Proof.
  unfold problem_121_spec.
  eapply (soep_skip 0%nat [1%nat; 2%nat; 3%nat; 4%nat; 5%nat; 6%nat; 7%nat; 6%nat] 0%nat 0%nat).
  - right; reflexivity.
  - eapply (soep_skip 1%nat [2%nat; 3%nat; 4%nat; 5%nat; 6%nat; 7%nat; 6%nat] 1%nat 0%nat).
    + left; reflexivity.
    + eapply (soep_skip 2%nat [3%nat; 4%nat; 5%nat; 6%nat; 7%nat; 6%nat] 2%nat 0%nat).
      * right; reflexivity.
      * eapply (soep_skip 3%nat [4%nat; 5%nat; 6%nat; 7%nat; 6%nat] 3%nat 0%nat).
        { left; reflexivity. }
        { eapply (soep_skip 4%nat [5%nat; 6%nat; 7%nat; 6%nat] 4%nat 0%nat).
          { right; reflexivity. }
          { eapply (soep_skip 5%nat [6%nat; 7%nat; 6%nat] 5%nat 0%nat).
            { left; reflexivity. }
            { eapply (soep_skip 6%nat [7%nat; 6%nat] 6%nat 0%nat).
              { right; reflexivity. }
              { eapply (soep_skip 7%nat [6%nat] 7%nat 0%nat).
                { left; reflexivity. }
                { eapply (soep_skip 6%nat [] 8%nat 0%nat).
                  { right; reflexivity. }
                  { apply soep_nil. } } } } } }
Qed.