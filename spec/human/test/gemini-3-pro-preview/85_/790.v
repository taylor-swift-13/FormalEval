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

Example test_case : problem_85_spec [1%Z; 3%Z; 5%Z; 7%Z; 9%Z; 12%Z; 15%Z; 18%Z; 15%Z] 30%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 1. Odd index? No. *)
  apply seao_other.
  - left. simpl. reflexivity.
  - (* Index 1: 3. Odd index? Yes. Even value? No. *)
    apply seao_other.
    + right. simpl. reflexivity.
    + (* Index 2: 5. Odd index? No. *)
      apply seao_other.
      * left. simpl. reflexivity.
      * (* Index 3: 7. Odd index? Yes. Even value? No. *)
        apply seao_other.
        -- right. simpl. reflexivity.
        -- (* Index 4: 9. Odd index? No. *)
           apply seao_other.
           ++ left. simpl. reflexivity.
           ++ (* Index 5: 12. Odd index? Yes. Even value? Yes. *)
              (* 30 = 12 + 18 *)
              replace 30 with (12 + 18) by reflexivity.
              apply seao_odd_even.
              ** simpl. reflexivity.
              ** simpl. reflexivity.
              ** (* Index 6: 15. Odd index? No. *)
                 apply seao_other.
                 --- left. simpl. reflexivity.
                 --- (* Index 7: 18. Odd index? Yes. Even value? Yes. *)
                     (* 18 = 18 + 0 *)
                     replace 18 with (18 + 0) by reflexivity.
                     apply seao_odd_even.
                     +++ simpl. reflexivity.
                     +++ simpl. reflexivity.
                     +++ (* Index 8: 15. Odd index? No. *)
                         apply seao_other.
                         *** left. simpl. reflexivity.
                         *** (* Index 9: nil. *)
                             apply seao_nil.
Qed.