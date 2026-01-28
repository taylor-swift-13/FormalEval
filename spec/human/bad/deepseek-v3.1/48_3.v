Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example test_all_a :
  problem_48_spec "aaaaa" true.
Proof.
  unfold problem_48_spec.
  split.
  - intros _ i Hlt.
    rewrite String.get_left_inbound in *.
    rewrite String.get_right_inbound in *.
    remember (String.length "aaaaa") as n.
    assert (Hlen: n = 5) by reflexivity.
    subst n.
    simpl.
    rewrite String.get_app_ge.
    + simpl.
      destruct (lt_dec i (length "aaaaa" / 2)). (* i < 2 *)
      * reflexivity.
      * exfalso.
        lia.
    + intros.
      lia.
    + lia.
  - intros _.
    reflexivity.
Qed.