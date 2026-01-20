Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Definition is_happy_spec (s : string) (res : bool) : Prop :=
  res = true <-> 
    (String.length s >= 3 /\
     forall i : nat, i < String.length s - 2 ->
       match String.get i s, String.get (i + 1) s, String.get (i + 2) s with
       | Some c1, Some c2, Some c3 => c1 <> c2 /\ c1 <> c3 /\ c2 <> c3
       | _, _, _ => False
       end).

Example test_case : is_happy_spec "bacbacb" true.
Proof.
  unfold is_happy_spec.
  split.
  - intros _.
    split.
    + simpl. repeat constructor.
    + intros i Hi.
      simpl in Hi.
      do 5 (destruct i; [ simpl; split; [discriminate | split; discriminate] | apply Lt.lt_S_n in Hi ]).
      exfalso. apply Nat.nlt_0_r in Hi. assumption.
  - intros _. reflexivity.
Qed.