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

Example test_case : problem_85_spec [1; 3; 5; 12; 7; 9; 920; 12; 919; 15; 18; 920; 920] 944.
Proof.
  unfold problem_85_spec.
  (* i=0, val=1. odd 0 = false. *)
  apply seao_other. { left. reflexivity. }
  (* i=1, val=3. odd 1 = true, even 3 = false. *)
  apply seao_other. { right. reflexivity. }
  (* i=2, val=5. odd 2 = false. *)
  apply seao_other. { left. reflexivity. }
  (* i=3, val=12. odd 3 = true, even 12 = true. 944 = 12 + 932. *)
  change 944 with (12 + 932).
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* i=4, val=7. odd 4 = false. *)
  apply seao_other. { left. reflexivity. }
  (* i=5, val=9. odd 5 = true, even 9 = false. *)
  apply seao_other. { right. reflexivity. }
  (* i=6, val=920. odd 6 = false. *)
  apply seao_other. { left. reflexivity. }
  (* i=7, val=12. odd 7 = true, even 12 = true. 932 = 12 + 920. *)
  change 932 with (12 + 920).
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* i=8, val=919. odd 8 = false. *)
  apply seao_other. { left. reflexivity. }
  (* i=9, val=15. odd 9 = true, even 15 = false. *)
  apply seao_other. { right. reflexivity. }
  (* i=10, val=18. odd 10 = false. *)
  apply seao_other. { left. reflexivity. }
  (* i=11, val=920. odd 11 = true, even 920 = true. 920 = 920 + 0. *)
  change 920 with (920 + 0).
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* i=12, val=920. odd 12 = false. *)
  apply seao_other. { left. reflexivity. }
  (* i=13, nil. *)
  apply seao_nil.
Qed.