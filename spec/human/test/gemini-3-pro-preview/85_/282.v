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

Example test_case : problem_85_spec [122%Z; 9%Z; 6%Z; 10%Z; 11%Z; 13%Z; 15%Z; 13%Z; 10%Z] 10%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 122. Odd 0 = false. Use seao_other (left). *)
  apply seao_other.
  - left. simpl. reflexivity.
  - (* Index 1: 9. Odd 1 = true, Even 9 = false. Use seao_other (right). *)
    apply seao_other.
    + right. simpl. reflexivity.
    + (* Index 2: 6. Odd 2 = false. Use seao_other (left). *)
      apply seao_other.
      * left. simpl. reflexivity.
      * (* Index 3: 10. Odd 3 = true, Even 10 = true. Use seao_odd_even. *)
        replace 10%Z with (10 + 0)%Z by reflexivity.
        apply seao_odd_even.
        -- simpl. reflexivity.
        -- simpl. reflexivity.
        -- (* Index 4: 11. Odd 4 = false. Use seao_other (left). *)
           apply seao_other.
           ++ left. simpl. reflexivity.
           ++ (* Index 5: 13. Odd 5 = true, Even 13 = false. Use seao_other (right). *)
              apply seao_other.
              ** right. simpl. reflexivity.
              ** (* Index 6: 15. Odd 6 = false. Use seao_other (left). *)
                 apply seao_other.
                 --- left. simpl. reflexivity.
                 --- (* Index 7: 13. Odd 7 = true, Even 13 = false. Use seao_other (right). *)
                     apply seao_other.
                     +++ right. simpl. reflexivity.
                     +++ (* Index 8: 10. Odd 8 = false. Use seao_other (left). *)
                         apply seao_other.
                         *** left. simpl. reflexivity.
                         *** (* Nil. *)
                             apply seao_nil.
Qed.