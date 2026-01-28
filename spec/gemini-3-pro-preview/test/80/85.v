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

Example test_case : is_happy_spec " t his   thish i  s b abatis bat" false.
Proof.
  unfold is_happy_spec.
  split.
  - intros H. discriminate H.
  - intros [Hlen Hdist].
    (* The string contains three consecutive spaces at index 6 *)
    specialize (Hdist 6).
    assert (Hbound : 6 < String.length " t his   thish i  s b abatis bat" - 2).
    { simpl. repeat constructor. }
    apply Hdist in Hbound.
    simpl in Hbound.
    destruct Hbound as [Hneq _].
    exfalso.
    apply Hneq.
    reflexivity.
Qed.