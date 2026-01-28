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

Example test_case : problem_85_spec [2%Z; 4%Z; 6%Z; 8%Z; 10%Z; 11%Z; 13%Z; 15%Z] 12%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 2. Even index. *)
  apply seao_other.
  - left. simpl. reflexivity.
  - (* Index 1: 4. Odd index, even value. *)
    replace 12%Z with (4 + 8)%Z by reflexivity.
    apply seao_odd_even.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + (* Index 2: 6. Even index. *)
      apply seao_other.
      * left. simpl. reflexivity.
      * (* Index 3: 8. Odd index, even value. *)
        replace 8%Z with (8 + 0)%Z by reflexivity.
        apply seao_odd_even.
        -- simpl. reflexivity.
        -- simpl. reflexivity.
        -- (* Index 4: 10. Even index. *)
           apply seao_other.
           ++ left. simpl. reflexivity.
           ++ (* Index 5: 11. Odd index, odd value. *)
              apply seao_other.
              ** right. simpl. reflexivity.
              ** (* Index 6: 13. Even index. *)
                 apply seao_other.
                 --- left. simpl. reflexivity.
                 --- (* Index 7: 15. Odd index, odd value. *)
                     apply seao_other.
                     +++ right. simpl. reflexivity.
                     +++ (* End of list *)
                         apply seao_nil.
Qed.