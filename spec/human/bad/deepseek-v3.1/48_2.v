Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example test_aba_string : 
  problem_48_spec "aba" true.
Proof.
  unfold problem_48_spec.
  split.
  - intros H i Hlt.
    (* Here, input = "aba", length = 3 *)
    (* For each i < 3/2 = 1 (i.e., i=0) *)
    simpl.
    (* i=0 *)
    simpl in Hlt.
    (* Since (0 < 1) is true, we need to show String.get 0 "aba" = String.get (3-1-0) "aba" = String.get 2 "aba" *)
    (* Compute String.get 0 "aba" *)
    compute.
    reflexivity.
  - intros H.
    (* to show String.get 0 "aba" = String.get 2 "aba" *)
    rewrite String.get_eq with (s:="aba") (n:=0).
    rewrite String.get_eq with (s:="aba") (n:=2).
    reflexivity.
Qed.