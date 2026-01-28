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

Example test_case : problem_85_spec [3%Z; 6%Z; 2%Z; 7%Z; 4%Z; 8%Z; 1%Z; 9%Z; 10%Z; 2%Z] 16%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 3. Odd index? No. *)
  apply seao_other.
  - left. reflexivity.
  - (* Index 1: 6. Odd index? Yes. Even value? Yes. 16 = 6 + 10. *)
    replace 16 with (6 + 10) by reflexivity.
    apply seao_odd_even.
    + reflexivity.
    + reflexivity.
    + (* Index 2: 2. Odd index? No. *)
      apply seao_other.
      * left. reflexivity.
      * (* Index 3: 7. Odd index? Yes. Even value? No. *)
        apply seao_other.
        -- right. reflexivity.
        -- (* Index 4: 4. Odd index? No. *)
           apply seao_other.
           ++ left. reflexivity.
           ++ (* Index 5: 8. Odd index? Yes. Even value? Yes. 10 = 8 + 2. *)
              replace 10 with (8 + 2) by reflexivity.
              apply seao_odd_even.
              ** reflexivity.
              ** reflexivity.
              ** (* Index 6: 1. Odd index? No. *)
                 apply seao_other.
                 --- left. reflexivity.
                 --- (* Index 7: 9. Odd index? Yes. Even value? No. *)
                     apply seao_other.
                     +++ right. reflexivity.
                     +++ (* Index 8: 10. Odd index? No. *)
                         apply seao_other.
                         *** left. reflexivity.
                         *** (* Index 9: 2. Odd index? Yes. Even value? Yes. 2 = 2 + 0. *)
                             replace 2 with (2 + 0) by reflexivity.
                             apply seao_odd_even.
                             ---- reflexivity.
                             ---- reflexivity.
                             ---- apply seao_nil.
Qed.