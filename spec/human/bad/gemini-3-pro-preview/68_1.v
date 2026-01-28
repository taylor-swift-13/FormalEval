Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Definition problem_68_pre (arr : list nat) : Prop := True.

(* pluck 函数的程序规约 *)
Definition problem_68_spec (arr : list nat) (output : option (nat * nat)) : Prop :=
  match output with
  | None => (* 情况1: 输出为空 *)
    (* 当且仅当列表中没有偶数时，输出为 None *)
    forall val, In val arr -> Nat.even val = false
  | Some (v, i) => (* 情况2: 输出为 Some (v, i) *)
    (* 1. v 必须是 arr 中索引为 i 的元素 *)
    i < length arr /\ nth i arr 1 = v /\
    (* 2. v 必须是偶数 *)
    Nat.even v = true/\
    (* 3. v 必须是 arr 中所有偶数里最小的值 *)
    (forall val, In val arr -> Nat.even val = true -> v <= val) /\
    (* 4. i 必须是 v 在 arr 中首次出现的最小索引 *)
    (forall j, j < i -> nth j arr 1 <> v)
  end.

Example test_case_pluck : problem_68_spec [4; 2; 3] (Some (2, 1)).
Proof.
  unfold problem_68_spec.
  repeat split.
  - (* 1 < length *)
    simpl. lia.
  - (* nth 1 = 2 *)
    simpl. reflexivity.
  - (* even 2 *)
    simpl. reflexivity.
  - (* minimal even *)
    intros val Hin Heven.
    simpl in Hin.
    destruct Hin as [H | [H | [H | H]]].
    + (* val = 4 *)
      rewrite <- H. lia.
    + (* val = 2 *)
      rewrite <- H. lia.
    + (* val = 3 *)
      rewrite <- H in Heven.
      simpl in Heven. discriminate.
    + (* False *)
      contradiction.
  - (* minimal index *)
    intros j Hj.
    assert (j = 0) by lia.
    subst j.
    simpl.
    intro H.
    discriminate.
Qed.