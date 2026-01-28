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

Example test_case : problem_85_spec [3%Z; 6%Z; 1%Z; 7%Z; 4%Z; 8%Z; 1%Z; 0%Z; 9%Z; 5%Z; 0%Z] 14%Z.
Proof.
  unfold problem_85_spec.
  (* i=0, val=3. Even index -> skip *)
  apply seao_other.
  - left. simpl. reflexivity.
  - (* i=1, val=6. Odd index, Even val -> add *)
    replace 14%Z with (6 + 8)%Z by reflexivity.
    apply seao_odd_even.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + (* i=2, val=1. Even index -> skip *)
      apply seao_other.
      * left. simpl. reflexivity.
      * (* i=3, val=7. Odd index, Odd val -> skip *)
        apply seao_other.
        -- right. simpl. reflexivity.
        -- (* i=4, val=4. Even index -> skip *)
           apply seao_other.
           ++ left. simpl. reflexivity.
           ++ (* i=5, val=8. Odd index, Even val -> add *)
              replace 8%Z with (8 + 0)%Z by reflexivity.
              apply seao_odd_even.
              ** simpl. reflexivity.
              ** simpl. reflexivity.
              ** (* i=6, val=1. Even index -> skip *)
                 apply seao_other.
                 --- left. simpl. reflexivity.
                 --- (* i=7, val=0. Odd index, Even val -> add *)
                     replace 0%Z with (0 + 0)%Z by reflexivity.
                     apply seao_odd_even.
                     +++ simpl. reflexivity.
                     +++ simpl. reflexivity.
                     +++ (* i=8, val=9. Even index -> skip *)
                         apply seao_other.
                         *** left. simpl. reflexivity.
                         *** (* i=9, val=5. Odd index, Odd val -> skip *)
                             apply seao_other.
                             ---- right. simpl. reflexivity.
                             ---- (* i=10, val=0. Even index -> skip *)
                                  apply seao_other.
                                  ++++ left. simpl. reflexivity.
                                  ++++ (* i=11, nil *)
                                       apply seao_nil.
Qed.