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

Example test_case : problem_121_spec [22; 33; 100; 65; 55; 66; 56; 99; 21; 0; 22; 33; 88] 76.
Proof.
  unfold problem_121_spec.
  (* Index 0: 22. Even index, even value. Skip. *)
  apply soep_skip. right. reflexivity.
  (* Index 1: 33. Odd index. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 2: 100. Even index, even value. Skip. *)
  apply soep_skip. right. reflexivity.
  (* Index 3: 65. Odd index. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 4: 55. Even index, odd value. Match. Need 55 + 21 = 76. *)
  apply soep_match with (s_tail := 21).
  - reflexivity.
  - reflexivity.
  - (* Index 5: 66. Odd index. Skip. *)
    apply soep_skip. left. reflexivity.
    (* Index 6: 56. Even index, even value. Skip. *)
    apply soep_skip. right. reflexivity.
    (* Index 7: 99. Odd index. Skip. *)
    apply soep_skip. left. reflexivity.
    (* Index 8: 21. Even index, odd value. Match. Need 21 + 0 = 21. *)
    apply soep_match with (s_tail := 0).
    + reflexivity.
    + reflexivity.
    + (* Index 9: 0. Odd index. Skip. *)
      apply soep_skip. left. reflexivity.
      (* Index 10: 22. Even index, even value. Skip. *)
      apply soep_skip. right. reflexivity.
      (* Index 11: 33. Odd index. Skip. *)
      apply soep_skip. left. reflexivity.
      (* Index 12: 88. Even index, even value. Skip. *)
      apply soep_skip. right. reflexivity.
      (* Nil *)
      apply soep_nil.
Qed.