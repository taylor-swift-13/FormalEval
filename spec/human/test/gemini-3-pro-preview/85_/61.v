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

Example test_case : problem_85_spec [21%Z; 5%Z; 3%Z; 6%Z; 64%Z; 5%Z; 2%Z] 6%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 21. Odd index? False. Use seao_other. *)
  apply seao_other.
  - left. reflexivity.
  - (* Index 1: 5. Odd index? True. Even value? False. Use seao_other. *)
    apply seao_other.
    + right. reflexivity.
    + (* Index 2: 3. Odd index? False. Use seao_other. *)
      apply seao_other.
      * left. reflexivity.
      * (* Index 3: 6. Odd index? True. Even value? True. Use seao_odd_even. *)
        replace 6%Z with (6 + 0)%Z by reflexivity.
        apply seao_odd_even.
        -- reflexivity.
        -- reflexivity.
        -- (* Index 4: 64. Odd index? False. Use seao_other. *)
           apply seao_other.
           ++ left. reflexivity.
           ++ (* Index 5: 5. Odd index? True. Even value? False. Use seao_other. *)
              apply seao_other.
              ** right. reflexivity.
              ** (* Index 6: 2. Odd index? False. Use seao_other. *)
                 apply seao_other.
                 --- left. reflexivity.
                 --- (* End of list *)
                     apply seao_nil.
Qed.