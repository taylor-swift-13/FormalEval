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

Example test_case : problem_85_spec [3%Z; 6%Z; 5%Z; 7%Z; 920%Z; 9%Z; 920%Z; 12%Z; 15%Z; 18%Z] 36%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 3. Not odd. *)
  apply seao_other.
  - left. simpl. reflexivity.
  - (* Index 1: 6. Odd, even. Add 6. *)
    replace 36%Z with (6 + 30)%Z by reflexivity.
    apply seao_odd_even.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + (* Index 2: 5. Not odd. *)
      apply seao_other.
      * left. simpl. reflexivity.
      * (* Index 3: 7. Odd, not even. *)
        apply seao_other.
        -- right. simpl. reflexivity.
        -- (* Index 4: 920. Not odd. *)
           apply seao_other.
           ++ left. simpl. reflexivity.
           ++ (* Index 5: 9. Odd, not even. *)
              apply seao_other.
              ** right. simpl. reflexivity.
              ** (* Index 6: 920. Not odd. *)
                 apply seao_other.
                 --- left. simpl. reflexivity.
                 --- (* Index 7: 12. Odd, even. Add 12. *)
                     replace 30%Z with (12 + 18)%Z by reflexivity.
                     apply seao_odd_even.
                     +++ simpl. reflexivity.
                     +++ simpl. reflexivity.
                     +++ (* Index 8: 15. Not odd. *)
                         apply seao_other.
                         *** left. simpl. reflexivity.
                         *** (* Index 9: 18. Odd, even. Add 18. *)
                             replace 18%Z with (18 + 0)%Z by reflexivity.
                             apply seao_odd_even.
                             ---- simpl. reflexivity.
                             ---- simpl. reflexivity.
                             ---- apply seao_nil.
Qed.