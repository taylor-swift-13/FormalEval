Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.

Inductive sum_odd_in_even_pos_rel : list nat -> nat -> nat -> Prop :=
| soep_nil : forall i, sum_odd_in_even_pos_rel nil i 0%nat
| soep_match : forall h t i s_tail, Nat.even i = true -> Nat.even h = false ->
    sum_odd_in_even_pos_rel t (S i) s_tail ->
    sum_odd_in_even_pos_rel (h :: t) i (h + s_tail)
| soep_skip : forall h t i s_tail, (Nat.even i = false \/ Nat.even h = true) ->
    sum_odd_in_even_pos_rel t (S i) s_tail ->
    sum_odd_in_even_pos_rel (h :: t) i s_tail.

(* 非空整数列表 *)
Definition problem_121_pre (l : list nat) : Prop := l <> [].

Definition problem_121_spec (l : list nat) (output : nat) : Prop :=
  sum_odd_in_even_pos_rel l 0%nat output.

Example test_case : problem_121_spec [0; 53; 2; 3; 6; 5; 75; 7; 8; 9; 10] 75.
Proof.
  unfold problem_121_spec.
  (* Index 0: 0. Even pos, Even val. Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 1: 53. Odd pos. Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 2: 2. Even pos, Even val. Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 3: 3. Odd pos. Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 4: 6. Even pos, Even val. Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 5: 5. Odd pos. Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 6: 75. Even pos, Odd val. Match. *)
  apply soep_match with (s_tail := 0).
  - reflexivity.
  - reflexivity.
  - (* Index 7: 7. Odd pos. Skip. *)
    apply soep_skip. { left. reflexivity. }
    (* Index 8: 8. Even pos, Even val. Skip. *)
    apply soep_skip. { right. reflexivity. }
    (* Index 9: 9. Odd pos. Skip. *)
    apply soep_skip. { left. reflexivity. }
    (* Index 10: 10. Even pos, Even val. Skip. *)
    apply soep_skip. { right. reflexivity. }
    (* Nil *)
    apply soep_nil.
Qed.