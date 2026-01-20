Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Local Open Scope string_scope.

Definition is_happy_spec (s : string) (res : bool) : Prop :=
  res = true <-> 
    (String.length s >= 3 /\
     forall i : nat, i < String.length s - 2 ->
       match String.get i s, String.get (i + 1) s, String.get (i + 2) s with
       | Some c1, Some c2, Some c3 => c1 <> c2 /\ c1 <> c3 /\ c2 <> c3
       | _, _, _ => False
       end).

Example test_case : is_happy_spec "xxyzycxyz" false.
Proof.
  unfold is_happy_spec.
  split.
  - intros H. discriminate H.
  - intros [Hlen Hcond].
    specialize (Hcond 0).
    simpl in Hcond.
    assert (Hbound : 0 < 7). { repeat constructor. }
    apply Hcond in Hbound.
    destruct Hbound as [Hcontra _].
    elim Hcontra. reflexivity.
Qed.