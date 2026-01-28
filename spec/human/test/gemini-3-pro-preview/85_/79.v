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

Example test_case : problem_85_spec [2%Z; 3%Z; 4%Z; 8%Z; 2%Z] 8%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 2. Odd 0 = false. *)
  apply seao_other.
  - left. reflexivity.
  - (* Index 1: 3. Odd 1 = true, Even 3 = false. *)
    apply seao_other.
    + right. reflexivity.
    + (* Index 2: 4. Odd 2 = false. *)
      apply seao_other.
      * left. reflexivity.
      * (* Index 3: 8. Odd 3 = true, Even 8 = true. *)
        replace 8 with (8 + 0) by reflexivity.
        apply seao_odd_even.
        -- reflexivity.
        -- reflexivity.
        -- (* Index 4: 2. Odd 4 = false. *)
           apply seao_other.
           ++ left. reflexivity.
           ++ apply seao_nil.
Qed.