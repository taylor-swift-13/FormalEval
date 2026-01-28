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

Example test_case : problem_85_spec [13%Z; 5%Z; 8%Z; 12%Z; 15%Z] 12%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 13. odd 0 = false. Use seao_other. *)
  apply seao_other.
  - left. simpl. reflexivity.
  - (* Index 1: 5. odd 1 = true, even 5 = false. Use seao_other. *)
    apply seao_other.
    + right. simpl. reflexivity.
    + (* Index 2: 8. odd 2 = false. Use seao_other. *)
      apply seao_other.
      * left. simpl. reflexivity.
      * (* Index 3: 12. odd 3 = true, even 12 = true. Use seao_odd_even. *)
        replace 12%Z with (12 + 0)%Z by reflexivity.
        apply seao_odd_even.
        -- simpl. reflexivity.
        -- simpl. reflexivity.
        -- (* Index 4: 15. odd 4 = false. Use seao_other. *)
           apply seao_other.
           ++ left. simpl. reflexivity.
           ++ (* Nil *)
              apply seao_nil.
Qed.