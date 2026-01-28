Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import Lia.
Import ListNotations.
Open Scope string_scope.

Definition problem_80_pre (s : string) : Prop := True.

Definition problem_80_spec (s : string) (output : bool) : Prop :=
  let len := String.length s in
  match output with
  | true =>
    (len >= 3)%nat /\
    (forall i : nat, (i + 2 < len)%nat ->
      let default_char := Ascii.ascii_of_nat 0 in
      let c1 := String.get i s in
      let c2 := String.get (i + 1) s in
      let c3 := String.get (i + 2) s in
      c1 <> c2 /\ c1 <> c3 /\ c2 <> c3)
  | false =>
    (len < 3)%nat \/
    (exists i : nat, (i + 2 < len)%nat /\
      (let default_char := Ascii.ascii_of_nat 0 in
       let c1 := String.get i s in
       let c2 := String.get (i + 1) s in
       let c3 := String.get (i + 2) s in
       c1 = c2 \/ c1 = c3 \/ c2 = c3))
  end.

Example test_problem_80_bacbacb_true : problem_80_spec "bacbacb" true.
Proof.
  unfold problem_80_spec.
  simpl.
  split.
  - lia.
  - intros i H.
    destruct i as [| i1 ].
    + simpl. repeat split; congruence.
    + destruct i1 as [| i2 ].
      * simpl. repeat split; congruence.
      * destruct i2 as [| i3 ].
        -- simpl. repeat split; congruence.
        -- destruct i3 as [| i4 ].
           ++ simpl. repeat split; congruence.
           ++ destruct i4 as [| i5 ].
              ** simpl. repeat split; congruence.
              ** exfalso; lia.
Qed.