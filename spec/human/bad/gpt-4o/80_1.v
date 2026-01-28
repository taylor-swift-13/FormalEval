Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

Definition problem_80_spec (s : string) (output : bool) : Prop :=
  let len := String.length s in
  match output with
  | true => (* "快乐"的条件 *)
    (len >= 3)%nat /\
    (forall i : nat, (i + 2 < len)%nat ->
      let default_char := Ascii.ascii_of_nat 0 in (* 提供一个默认值，尽管在卫士保护下不会被使用 *)
      let c1 := String.get i s in
      let c2 := String.get (i + 1) s in
      let c3 := String.get (i + 2) s in
      c1 <> c2 /\ c1 <> c3 /\ c2 <> c3)
  | false => (* "不快乐"的条件 *)
    (len < 3)%nat \/
    (exists i : nat, (i + 2 < len)%nat /\
      (let default_char := Ascii.ascii_of_nat 0 in
       let c1 := String.get i s in
       let c2 := String.get (i + 1) s in
       let c3 := String.get (i + 2) s in
       c1 = c2 \/ c1 = c3 \/ c2 = c3))
  end.

Example test_case_1 : problem_80_spec "a" false.
Proof.
  unfold problem_80_spec.
  simpl.
  left.
  lia.
Qed.