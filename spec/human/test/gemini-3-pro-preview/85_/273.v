Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Bool.Bool Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Inductive sum_even_at_odd_indices_rel : list Z -> nat -> Z -> Prop :=
| seao_nil : forall i, sum_even_at_odd_indices_rel nil i 0%Z
| seao_odd_even : forall h t i s_tail, Nat.odd i = true -> Z.even h = true ->
    sum_even_at_odd_indices_rel t (S i) s_tail ->
    sum_even_at_odd_indices_rel (h :: t) i (h + s_tail)
| seao_other : forall h t i s_tail, (Nat.odd i = false \/ Z.even h = false) ->
    sum_even_at_odd_indices_rel t (S i) s_tail ->
    sum_even_at_odd_indices_rel (h :: t) i s_tail.

Definition problem_85_pre (lst : list Z) : Prop := lst <> []%list.

Definition problem_85_spec (lst : list Z) (output : Z) : Prop :=
  sum_even_at_odd_indices_rel lst 0%nat output.

Example test_case : problem_85_spec [2%Z; 8%Z; 10%Z; 11%Z; 7%Z; 2%Z] 10%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0, val 2: even index -> skip *)
  apply seao_other.
  - left. simpl. reflexivity.
  - (* Index 1, val 8: odd index, even val -> add 8. Remainder sum needs to be 2. *)
    replace 10%Z with (8 + 2)%Z by reflexivity.
    apply seao_odd_even.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + (* Index 2, val 10: even index -> skip *)
      apply seao_other.
      * left. simpl. reflexivity.
      * (* Index 3, val 11: odd index, odd val -> skip *)
        apply seao_other.
        -- right. simpl. reflexivity.
        -- (* Index 4, val 7: even index -> skip *)
           apply seao_other.
           ++ left. simpl. reflexivity.
           ++ (* Index 5, val 2: odd index, even val -> add 2. Remainder sum needs to be 0. *)
              replace 2%Z with (2 + 0)%Z by reflexivity.
              apply seao_odd_even.
              ** simpl. reflexivity.
              ** simpl. reflexivity.
              ** (* Index 6, nil -> 0 *)
                 apply seao_nil.
Qed.