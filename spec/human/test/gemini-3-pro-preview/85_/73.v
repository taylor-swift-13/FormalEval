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

Example test_case : problem_85_spec [7%Z; 2%Z; 3%Z; 5%Z; 4%Z; 4%Z; 9%Z; 4%Z; 2%Z] 10%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 7. Odd 0 = false. Use seao_other. *)
  apply seao_other.
  - left. reflexivity.
  - (* Index 1: 2. Odd 1 = true. Even 2 = true. Use seao_odd_even. *)
    replace 10%Z with (2 + 8)%Z by reflexivity.
    apply seao_odd_even.
    + reflexivity.
    + reflexivity.
    + (* Index 2: 3. Odd 2 = false. Use seao_other. *)
      apply seao_other.
      * left. reflexivity.
      * (* Index 3: 5. Odd 3 = true. Even 5 = false. Use seao_other. *)
        apply seao_other.
        -- right. reflexivity.
        -- (* Index 4: 4. Odd 4 = false. Use seao_other. *)
           apply seao_other.
           ++ left. reflexivity.
           ++ (* Index 5: 4. Odd 5 = true. Even 4 = true. Use seao_odd_even. *)
              replace 8%Z with (4 + 4)%Z by reflexivity.
              apply seao_odd_even.
              ** reflexivity.
              ** reflexivity.
              ** (* Index 6: 9. Odd 6 = false. Use seao_other. *)
                 apply seao_other.
                 --- left. reflexivity.
                 --- (* Index 7: 4. Odd 7 = true. Even 4 = true. Use seao_odd_even. *)
                     replace 4%Z with (4 + 0)%Z by reflexivity.
                     apply seao_odd_even.
                     +++ reflexivity.
                     +++ reflexivity.
                     +++ (* Index 8: 2. Odd 8 = false. Use seao_other. *)
                         apply seao_other.
                         *** left. reflexivity.
                         *** (* Index 9: nil. Use seao_nil. *)
                             apply seao_nil.
Qed.