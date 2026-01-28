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

Example test_case : is_happy_spec "abbaacbacbcabc" false.
Proof.
  unfold is_happy_spec.
  split.
  - intros H. discriminate H.
  - intros [Hlen Hforall].
    specialize (Hforall 0).
    simpl in Hforall.
    assert (Hcond : 0 < 12).
    { repeat constructor. }
    apply Hforall in Hcond.
    destruct Hcond as [_ [_ Hcontra]].
    exfalso.
    apply Hcontra.
    reflexivity.
Qed.